package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.passes.Pass
import firrtl.transforms.DontTouchAnnotation

import scala.collection.mutable

/** Replace Boolean constant case chains with equality reductions before balancing. */
object ReduceConstantMuxChains extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  val minChainLength = 8
  case class Stats(chains: Int = 0, muxes: Int = 0, longestChain: Int = 0)
  private val bit = UIntType(IntWidth(1))

  private def flattened(s: Statement): Seq[Statement] = s match {
    case b: Block => b.stmts.flatMap(flattened)
    case other => Seq(other)
  }

  private def reduceModule(m: Module, protectedNames: Set[String]): (Module, Stats) = {
    val statements = flattened(m.body)
    if (statements.exists(_.isInstanceOf[Conditionally])) return m -> Stats()
    val namespace = Namespace(m)
    val sinks = new java.util.IdentityHashMap[Statement, Seq[(Expression, DefNode)]]
    val sinkNodes = mutable.ArrayBuffer.empty[DefNode]
    statements.filterNot(_.isInstanceOf[DefNode]).foreach { s =>
      val roots = mutable.ArrayBuffer.empty[(Expression, DefNode)]
      s.mapExpr { e =>
        if (e.isInstanceOf[Mux]) {
          val n = DefNode(NoInfo, namespace.newName("__rteaal_case_root"), e)
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
        case r: Reference if definitions.contains(r.name) && seen.add(r.name) &&
            definitions(r.name).value.tpe == r.tpe =>
          names += r.name
          current = definitions(r.name).value
          true
        case _ => false
      }) {}
      current -> names.toVector
    }
    def literal(e: Expression): Option[UIntLiteral] = resolve(e)._1 match {
      case l @ UIntLiteral(value, IntWidth(w)) if w > 0 && value >= 0 && value.bitLength <= w => Some(l)
      case _ => None
    }
    def comparison(e: Expression): Option[Expression] = resolve(e)._1 match {
      case DoPrim(Eq, args, consts, tpe) if args.size == 2 && consts.isEmpty && tpe == bit =>
        val selector = (literal(args(0)), literal(args(1))) match {
          case (Some(_), None) => Some(args(1))
          case (None, Some(_)) => Some(args(0))
          case _ => None
        }
        selector.filter(_.tpe match {
          case UIntType(IntWidth(w)) => w > 0
          case _ => false
        })
      case _ => None
    }

    // Only inspect maximal false-branch chains, so an unsupported outer mux
    // cannot accidentally cause a matching suffix to be rewritten on its own.
    val children = candidates.flatMap { n =>
      resolve(n.value.asInstanceOf[Mux].fval)._2
    }.toSet
    val removed = mutable.HashSet.empty[String]
    val replacements = mutable.HashMap.empty[String, Seq[Statement]]
    var stats = Stats()
    candidates.filterNot(n => children(n.name) || protectedNames(n.name)).foreach { root =>
      val conditions = mutable.ArrayBuffer.empty[Expression]
      val consumed = mutable.HashSet.empty[String]
      val seen = mutable.HashSet.empty[String]
      var current = root.value
      var selector: Option[Expression] = None
      var hit: Option[BigInt] = None
      var valid = true
      var done = false
      while (valid && !done) {
        val (value, names) = resolve(current)
        valid = names.forall(name => seen.add(name) && uses(name) == 1 && !protectedNames(name))
        consumed ++= names
        value match {
          case mux: Mux if valid && mux.tpe == bit =>
            val address = comparison(mux.cond)
            val constant = literal(mux.tval).filter(_.tpe == bit).map(_.value)
            valid = address.nonEmpty && constant.nonEmpty &&
              selector.forall(s => s == address.get && s.tpe == address.get.tpe) &&
              hit.forall(_ == constant.get)
            if (valid) {
              selector = address
              hit = constant
              conditions += mux.cond
              current = mux.fval
            }
          case _ =>
            valid = valid && hit.nonEmpty && literal(value).exists(l =>
              l.tpe == bit && l.value == 1 - hit.get)
            done = true
        }
      }
      if (valid && conditions.size >= minChainLength) {
        val generated = mutable.ArrayBuffer.empty[Statement]
        var reduction = conditions.head
        conditions.tail.zipWithIndex.foreach { case (condition, i) =>
          val value = DoPrim(Or, Seq(reduction, condition), Seq.empty, bit)
          val isRoot = hit.contains(BigInt(1)) && i == conditions.size - 2
          val name = if (isRoot) root.name else namespace.newName("__rteaal_case_or")
          generated += DefNode(root.info, name, value)
          reduction = WRef(name, bit, NodeKind, SourceFlow)
        }
        if (hit.contains(BigInt(0)))
          generated += root.copy(value = DoPrim(Not, Seq(reduction), Seq.empty, bit))
        removed ++= consumed
        replacements(root.name) = generated.toVector
        stats = Stats(stats.chains + 1, stats.muxes + conditions.size,
          stats.longestChain.max(conditions.size))
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
    if (sys.props.get("rteaal.reduceConstantMuxChains").contains("false")) return state -> Stats()
    val protectedNames = state.annotations.collect { case DontTouchAnnotation(t) => t.module -> t.ref }
      .groupMap(_._1)(_._2).map { case (module, names) => module -> names.toSet }
    var total = Stats()
    val circuit = state.circuit.mapModule {
      case m: Module =>
        val (result, stats) = reduceModule(m, protectedNames.getOrElse(m.name, Set.empty))
        total = Stats(total.chains + stats.chains, total.muxes + stats.muxes,
          total.longestChain.max(stats.longestChain))
        result
      case other => other
    }
    state.copy(circuit = circuit) -> total
  }

  override def execute(state: CircuitState): CircuitState = executeWithStats(state)._1
  override def run(c: Circuit): Circuit = execute(CircuitState(c, Seq.empty)).circuit
}
