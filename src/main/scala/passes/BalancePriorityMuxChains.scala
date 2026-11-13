package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.passes.Pass
import firrtl.transforms.DontTouchAnnotation

import scala.collection.mutable

/** Balance ordered priority selection without assuming mutually exclusive hits. */
object BalancePriorityMuxChains extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  val minChainLength = 8
  case class Stats(chains: Int = 0, muxes: Int = 0, longestChain: Int = 0,
      lookupChainsSkipped: Int = 0)
  private val bit = UIntType(IntWidth(1))
  private val always = UIntLiteral(1, IntWidth(1))

  private def flattened(s: Statement): Seq[Statement] = s match {
    case b: Block => b.stmts.flatMap(flattened)
    case other => Seq(other)
  }

  private def balanceModule(m: Module, protectedNames: Set[String]): (Module, Stats) = {
    val statements = flattened(m.body)
    if (statements.exists(_.isInstanceOf[Conditionally])) return m -> Stats()
    val namespace = Namespace(m)
    val sinks = new java.util.IdentityHashMap[Statement, Seq[(Expression, DefNode)]]
    val sinkNodes = mutable.ArrayBuffer.empty[DefNode]
    statements.filterNot(_.isInstanceOf[DefNode]).foreach { s =>
      val roots = mutable.ArrayBuffer.empty[(Expression, DefNode)]
      s.mapExpr { e =>
        if (e.isInstanceOf[Mux]) {
          val n = DefNode(NoInfo, namespace.newName("__rteaal_priority_root"), e)
          roots += e -> n
          sinkNodes += n
        }
        e
      }
      if (roots.nonEmpty) sinks.put(s, roots.toVector)
    }
    val allNodes = statements.collect { case n: DefNode => n } ++ sinkNodes
    val definitions = allNodes.map(n => n.name -> n).toMap
    val candidates = allNodes.filter(_.value.isInstanceOf[Mux])
    if (candidates.isEmpty) return m -> Stats()
    val uses = mutable.HashMap.empty[String, Int].withDefaultValue(0)
    def count(e: Expression): Expression = {
      e match { case r: Reference => uses(r.name) += 1; case _ => }
      e.mapExpr(count)
      e
    }
    statements.foreach(_.mapExpr(count))

    def resolve(e: Expression): (Expression, Vector[String]) = {
      var current = e
      val names = mutable.ArrayBuffer.empty[String]
      val seen = mutable.HashSet.empty[String]
      while (current match {
        case r: Reference if definitions.contains(r.name) && seen.add(r.name) =>
          names += r.name
          current = definitions(r.name).value
          true
        case _ => false
      }) {}
      current -> names.toVector
    }
    def comparison(e: Expression): Option[(Expression, BigInt, BigInt)] = resolve(e)._1 match {
      case DoPrim(Eq, args, consts, tpe) if args.size == 2 && consts.isEmpty && tpe == bit =>
        val pair = (resolve(args(0))._1, resolve(args(1))._1) match {
          case (l: UIntLiteral, s) => Some(s -> l.value)
          case (s, l: UIntLiteral) => Some(s -> l.value)
          case _ => None
        }
        pair.flatMap { case (s, v) => s.tpe match {
          case UIntType(IntWidth(w)) if w > 0 && w < 31 && v >= 0 && v < (BigInt(1) << w.toInt) =>
            Some((s, w, v))
          case _ => None
        }}
      case _ => None
    }
    // Conservatively retain dense runs, including lookup subchains of a mixed
    // priority chain. Match the extractor's integer table-size/chain-size test.
    def hasLookup(conditions: Seq[Expression]): Boolean = {
      var selector: Option[(Expression, BigInt)] = None
      var length = 0
      conditions.exists { cond =>
        comparison(cond) match {
          case Some((s, w, _)) =>
            val key = s -> w
            length = if (selector.contains(key)) length + 1 else 1
            selector = Some(key)
            length > 2 && (BigInt(1) << w.toInt) / length < 4
          case None => selector = None; length = 0; false
        }
      }
    }

    val arrivals = mutable.HashMap.empty[String, Int]
    def depth(e: Expression, lookup: String => Int): Int = e match {
      case r: Reference => lookup(r.name)
      case _ =>
        var children = 0
        e.mapExpr { child => children = children.max(depth(child, lookup)); child }
        val cost = e match {
          case _: Literal | _: SubField | _: SubIndex => 0
          case DoPrim(Pad | AsUInt | AsSInt, _, _, _) => 0
          case _ => 1
        }
        children + cost
    }
    def references(e: Expression): List[String] = {
      val found = mutable.ArrayBuffer.empty[String]
      def visit(x: Expression): Expression = {
        x match { case r: Reference if definitions.contains(r.name) => found += r.name; case _ => }
        x.mapExpr(visit)
        x
      }
      visit(e)
      found.toList
    }
    def arrival(e: Expression): Int = {
      var pending = references(e).map(_ -> false)
      val visiting = mutable.HashSet.empty[String]
      while (pending.nonEmpty) {
        val (name, ready) = pending.head
        pending = pending.tail
        if (!arrivals.contains(name)) {
          if (ready) {
            arrivals(name) = depth(definitions(name).value, n => arrivals.getOrElse(n, 0))
            visiting -= name
          } else {
            require(visiting.add(name), s"Combinational cycle at ${m.name}.$name")
            pending = references(definitions(name).value).map(_ -> false) :::
              ((name -> true) :: pending)
          }
        }
      }
      depth(e, n => arrivals.getOrElse(n, 0))
    }

    // Inspect maximal false-branch chains only. Reject a whole chain if any
    // intermediate is shared/protected or has incompatible type information.
    val children = candidates.flatMap(n => resolve(n.value.asInstanceOf[Mux].fval)._2).toSet
    val removed = mutable.HashSet.empty[String]
    val replacements = mutable.HashMap.empty[String, Seq[Statement]]
    var stats = Stats()
    candidates.filterNot(n => children(n.name) || protectedNames(n.name)).foreach { root =>
      val entries = mutable.ArrayBuffer.empty[(Expression, Expression)]
      val consumed = mutable.HashSet.empty[String]
      val seen = mutable.HashSet.empty[String]
      val tpe = root.value.tpe
      var valid = tpe match { case UIntType(IntWidth(w)) => w > 0; case _ => false }
      var current = root.value
      var done = false
      while (valid && !done) {
        val (value, names) = resolve(current)
        value match {
          case mux: Mux =>
            valid = current.tpe == tpe && names.forall(name => seen.add(name) && uses(name) == 1 &&
              !protectedNames(name) && definitions(name).value.tpe == tpe) &&
              mux.cond.tpe == bit && mux.tpe == tpe && mux.tval.tpe == tpe && mux.fval.tpe == tpe
            if (valid) {
              consumed ++= names
              entries += mux.cond -> mux.tval
              current = mux.fval
            }
          case _ =>
            // Retain the original default expression and all its definitions.
            valid = current.tpe == tpe && value.tpe == tpe && !names.exists(consumed) &&
              names.forall(name => definitions(name).value.tpe == tpe)
            done = true
        }
      }
      if (valid && entries.size >= minChainLength) {
        if (hasLookup(entries.map(_._1).toVector))
          stats = stats.copy(lookupChainsSkipped = stats.lookupChainsSkipped + 1)
        else {
          val before = arrival(root.value)
          entries += always -> current
          val generated = mutable.ArrayBuffer.empty[Statement]
          def emit(e: Expression, name: String): Expression = {
            generated += DefNode(root.info, name, e)
            WRef(name, e.tpe, NodeKind, SourceFlow)
          }
          // Every segment has a first-hit value and a shared hit summary.
          // Concatenation is associative, but the high-to-low order is fixed.
          def tree(start: Int, end: Int, needHit: Boolean): (Expression, Expression) = {
            if (end - start == 1) return entries(start)
            val mid = start + (end - start) / 2
            val (hitA, valueA) = tree(start, mid, needHit = true)
            val (hitB, valueB) = tree(mid, end, needHit)
            val hit = if (!needHit || hitA == always || hitB == always) always
              else emit(DoPrim(Or, Seq(hitA, hitB), Seq.empty, bit),
                namespace.newName("__rteaal_priority_hit"))
            val name = if (start == 0 && end == entries.size) root.name
              else namespace.newName("__rteaal_priority_value")
            hit -> emit(Mux(hitA, valueA, valueB, tpe), name)
          }
          tree(0, entries.size, needHit = false)
          val newArrivals = mutable.HashMap.empty[String, Int]
          generated.foreach { case n: DefNode =>
            newArrivals(n.name) = depth(n.value,
              name => newArrivals.getOrElse(name, arrivals.getOrElse(name, 0)))
          }
          // Account for original condition/data arrival times, and avoid
          // rebalancing an already balanced tree's short false spine on reruns.
          if (newArrivals(root.name) < before) {
            removed ++= consumed
            replacements(root.name) = generated.toVector
            val length = entries.size - 1
            stats = stats.copy(chains = stats.chains + 1, muxes = stats.muxes + length,
              longestChain = stats.longestChain.max(length))
          }
        }
      }
    }
    if (replacements.isEmpty) m -> stats
    else {
      val body = statements.flatMap {
        case n: DefNode if replacements.contains(n.name) => replacements(n.name)
        case n: DefNode if removed(n.name) => Seq.empty
        case s if sinks.containsKey(s) =>
          val roots = sinks.get(s).filter { case (_, n) => replacements.contains(n.name) }
          val refs = new java.util.IdentityHashMap[Expression, Expression]
          roots.foreach { case (e, n) => refs.put(e, WRef(n.name, e.tpe, NodeKind, SourceFlow)) }
          roots.flatMap { case (_, n) => replacements(n.name) } :+
            s.mapExpr(e => if (refs.containsKey(e)) refs.get(e) else e)
        case s => Seq(s)
      }
      m.copy(body = Block(body)) -> stats
    }
  }

  def executeWithStats(state: CircuitState): (CircuitState, Stats) = {
    if (sys.props.get("rteaal.balancePriorityMuxChains").contains("false")) return state -> Stats()
    val protectedNames = state.annotations.collect { case DontTouchAnnotation(t) => t.module -> t.ref }
      .groupMap(_._1)(_._2).map { case (module, names) => module -> names.toSet }
    var total = Stats()
    val circuit = state.circuit.mapModule {
      case m: Module =>
        val (result, stats) = balanceModule(m, protectedNames.getOrElse(m.name, Set.empty))
        total = Stats(total.chains + stats.chains, total.muxes + stats.muxes,
          total.longestChain.max(stats.longestChain), total.lookupChainsSkipped + stats.lookupChainsSkipped)
        result
      case other => other
    }
    state.copy(circuit = circuit) -> total
  }

  override def execute(state: CircuitState): CircuitState = executeWithStats(state)._1
  override def run(c: Circuit): Circuit = execute(CircuitState(c, Seq.empty)).circuit
}
