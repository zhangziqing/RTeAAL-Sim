package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.passes.Pass
import firrtl.transforms.DontTouchAnnotation

import scala.collection.mutable

/** Expose bitwise reductions hidden by muxes before mux-chain optimization. */
object FactorMuxBitwise extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  case class Stats(andMuxes: Int = 0, orMuxes: Int = 0, xorMuxes: Int = 0,
      removedNodes: Int = 0, depthRejected: Int = 0) {
    def +(s: Stats): Stats = Stats(andMuxes + s.andMuxes, orMuxes + s.orMuxes,
      xorMuxes + s.xorMuxes, removedNodes + s.removedNodes, depthRejected + s.depthRejected)
  }

  private def flattened(s: Statement): Seq[Statement] = s match {
    case b: Block => b.stmts.flatMap(flattened)
    case other => Seq(other)
  }

  private def factorModule(m: Module, protectedNames: Set[String]): (Module, Stats) = {
    val statements = flattened(m.body)
    if (statements.exists(_.isInstanceOf[Conditionally])) return m -> Stats()
    val definitions = statements.collect { case n: DefNode => n.name -> n.value }.toMap
    val namespace = Namespace(m)
    val consumed = mutable.HashSet.empty[String]
    var stats = Stats()

    def references(e: Expression): Vector[String] = {
      val names = mutable.ArrayBuffer.empty[String]
      def visit(x: Expression): Expression = {
        x match { case r: Reference => names += r.name; case _ => }
        x.mapExpr(visit)
        x
      }
      visit(e)
      names.toVector
    }
    def aliases(e: Expression): Expression = {
      var current = e
      val seen = mutable.HashSet.empty[String]
      var done = false
      while (!done) current match {
        case r: Reference if !protectedNames(r.name) && seen.add(r.name) =>
          definitions.get(r.name) match {
            case Some(value: Reference) if value.tpe == r.tpe => current = value
            case Some(value: UIntLiteral) if value.tpe == r.tpe => current = value
            case _ => done = true
          }
        case _ => done = true
      }
      current
    }
    def same(a: Expression, b: Expression): Boolean = a.tpe == b.tpe && aliases(a) == aliases(b)
    def operation(e: Expression, tpe: Type): Option[(DoPrim, Vector[String])] = {
      var current = e
      val names = mutable.ArrayBuffer.empty[String]
      val seen = mutable.HashSet.empty[String]
      var done = false
      while (!done) current match {
        case r: Reference if !protectedNames(r.name) && seen.add(r.name) &&
            definitions.get(r.name).exists(_.tpe == r.tpe) =>
          names += r.name
          current = definitions(r.name)
        case _ => done = true
      }
      current match {
        case p @ DoPrim(And | Or | Xor, args, consts, result) if args.size == 2 &&
            consts.isEmpty && result == tpe && args.forall(_.tpe == tpe) =>
          Some(p -> names.toVector)
        case _ => None
      }
    }

    // Use the same local arrival model as associative balancing. Keep selector
    // paths from gaining a level when extracting a shallow common operand.
    val arrivals = mutable.HashMap.empty[String, Int]
    def expressionDepth(e: Expression): Int = e match {
      case r: Reference => arrivals.getOrElse(r.name, 0)
      case _: Literal | _: SubField | _: SubIndex => 0
      case _ =>
        var maximum = 0
        e.mapExpr { child => maximum = maximum.max(expressionDepth(child)); child }
        maximum + (e match { case DoPrim(Pad | AsUInt | AsSInt, _, _, _) => 0; case _ => 1 })
    }
    def arrival(e: Expression): Int = {
      var pending = references(e).filter(definitions.contains).map(_ -> false).toList
      val visiting = mutable.HashSet.empty[String]
      while (pending.nonEmpty) {
        val (name, ready) = pending.head
        pending = pending.tail
        if (!arrivals.contains(name)) {
          if (ready) {
            arrivals(name) = expressionDepth(definitions(name))
            visiting -= name
          } else {
            require(visiting.add(name), s"Combinational cycle at ${m.name}.$name")
            pending = references(definitions(name)).filter(definitions.contains)
              .map(_ -> false).toList ::: ((name -> true) :: pending)
          }
        }
      }
      expressionDepth(e)
    }

    case class Factor(op: PrimOp, common: Expression, t: Expression, f: Expression,
        names: Vector[String])
    def factor(mux: Mux): Option[Factor] = mux.tpe match {
      case UIntType(IntWidth(w)) if w > 0 && w.isValidInt && mux.cond.tpe == UIntType(IntWidth(1)) &&
          mux.tval.tpe == mux.tpe && mux.fval.tpe == mux.tpe =>
        val t = operation(mux.tval, mux.tpe)
        val f = operation(mux.fval, mux.tpe)
        val both = for {
          (a, an) <- t.toSeq
          (b, bn) <- f.toSeq if a.op == b.op
          ai <- a.args.indices
          bi <- b.args.indices if same(a.args(ai), b.args(bi))
        } yield Factor(a.op, a.args(ai), a.args(1 - ai), b.args(1 - bi), an ++ bn)
        def single(branch: Option[(DoPrim, Vector[String])], old: Expression,
            trueArm: Boolean): Option[Factor] = branch.flatMap { case (p, names) =>
          p.args.indices.find(i => same(p.args(i), old)).map { i =>
            val unit = UIntLiteral(if (p.op == And) (BigInt(1) << w.toInt) - 1 else BigInt(0), IntWidth(w))
            val other = p.args(1 - i)
            Factor(p.op, old, if (trueArm) other else unit,
              if (trueArm) unit else other, names)
          }
        }
        both.headOption.orElse(single(t, mux.fval, true)).orElse(single(f, mux.tval, false))
      case _ => None
    }

    val rewritten = statements.flatMap { statement =>
      val generated = mutable.ArrayBuffer.empty[Statement]
      def rewrite(e: Expression): Expression = {
        val mapped = e.mapExpr(rewrite)
        mapped match {
          case mux: Mux => factor(mux) match {
            case Some(f) =>
              val gateDepth = 1 + arrival(mux.cond).max(arrival(f.t)).max(arrival(f.f))
              if (1 + arrival(f.common).max(gateDepth) > arrival(mux)) {
                stats = stats.copy(depthRejected = stats.depthRejected + 1)
                mux
              } else {
                val name = namespace.newName("__rteaal_mux_bitwise")
                generated += DefNode(NoInfo, name, Mux(mux.cond, f.t, f.f, mux.tpe))
                consumed ++= f.names
                stats = f.op match {
                  case And => stats.copy(andMuxes = stats.andMuxes + 1)
                  case Or => stats.copy(orMuxes = stats.orMuxes + 1)
                  case Xor => stats.copy(xorMuxes = stats.xorMuxes + 1)
                }
                DoPrim(f.op, Seq(f.common, WRef(name, mux.tpe, NodeKind, SourceFlow)), Seq.empty, mux.tpe)
              }
            case None => mux
          }
          case _ => mapped
        }
      }
      val result = statement match {
        case n: DefNode if protectedNames(n.name) => n
        case other => other.mapExpr(rewrite)
      }
      generated.toVector :+ result
    }
    if (stats.andMuxes + stats.orMuxes + stats.xorMuxes == 0) return m -> stats
    // Dead branch operators would keep a second use of the accumulator alive
    // and prevent the following associative pass from seeing a single-use tree.
    val uses = mutable.HashMap.empty[String, Int].withDefaultValue(0)
    rewritten.foreach(_.mapExpr { e => references(e).foreach(n => uses(n) += 1); e })
    val finalDefinitions = rewritten.collect { case n: DefNode => n.name -> n.value }.toMap
    val pending = mutable.Queue.from(consumed.filter(n => uses(n) == 0 && !protectedNames(n)))
    val removed = mutable.HashSet.empty[String]
    while (pending.nonEmpty) {
      val name = pending.dequeue()
      if (removed.add(name)) references(finalDefinitions(name)).foreach { input =>
        uses(input) -= 1
        if (consumed(input) && uses(input) == 0 && !protectedNames(input)) pending.enqueue(input)
      }
    }
    m.copy(body = Block(rewritten.filterNot {
      case n: DefNode => removed(n.name)
      case _ => false
    })) -> stats.copy(removedNodes = removed.size)
  }

  def executeWithStats(state: CircuitState): (CircuitState, Stats) = {
    if (sys.props.get("rteaal.factorMuxBitwise").contains("false")) return state -> Stats()
    val protectedNames = state.annotations.collect { case DontTouchAnnotation(t) => t.module -> t.ref }
      .groupMap(_._1)(_._2).map { case (module, names) => module -> names.toSet }
    var total = Stats()
    val circuit = state.circuit.mapModule {
      case m: Module =>
        val (result, stats) = factorModule(m, protectedNames.getOrElse(m.name, Set.empty))
        total = total + stats
        result
      case other => other
    }
    state.copy(circuit = circuit) -> total
  }

  override def execute(state: CircuitState): CircuitState = executeWithStats(state)._1
  override def run(c: Circuit): Circuit = execute(CircuitState(c, Seq.empty)).circuit
}
