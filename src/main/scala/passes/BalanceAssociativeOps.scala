package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.passes.Pass
import firrtl.transforms.DontTouchAnnotation

import scala.collection.mutable

/** Reassociate full-precision integer trees without crossing observable intermediates. */
object BalanceAssociativeOps extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  private def width(t: Type): BigInt = t match {
    case UIntType(IntWidth(w)) => w
    case SIntType(IntWidth(w)) => w
    case _ => BigInt(0)
  }

  private def family(t: Type): Int = t match {
    case UIntType(IntWidth(w)) if w > 0 => 0
    case SIntType(IntWidth(w)) if w > 0 => 1
    case _ => -1
  }

  private def resultType(op: PrimOp, a: Type, b: Type): Type = {
    val w = op match {
      case Add => width(a).max(width(b)) + 1
      case Mul | Cat => width(a) + width(b)
      case _ => width(a).max(width(b))
    }
    if (family(a) == 1 && (op == Add || op == Mul)) SIntType(IntWidth(w))
    else UIntType(IntWidth(w))
  }

  private def eligible(p: DoPrim): Boolean = {
    val supported = p.op match {
      case Add | Mul => family(p.tpe) >= 0
      case And | Or | Xor | Cat => family(p.tpe) == 0
      case _ => false
    }
    supported && p.args.size == 2 && p.consts.isEmpty &&
      p.args.forall(a => family(a.tpe) == family(p.tpe)) &&
      p.tpe == resultType(p.op, p.args(0).tpe, p.args(1).tpe)
  }

  private def balanceModule(m: Module, protectedNames: Set[String]): Module = {
    val namespace = Namespace(m)

    def flattenBlocks(statement: Statement): Seq[Statement] = statement match {
      case block: Block => block.stmts.flatMap(flattenBlocks)
      case other => Seq(other)
    }

    def balanceStatement(statement: Statement): Statement = statement match {
      case EmptyStmt => EmptyStmt
      case block: Block => balanceBlock(block)
      case conditional: Conditionally =>
        conditional.copy(
          conseq = balanceStatement(conditional.conseq),
          alt = balanceStatement(conditional.alt))
      case node: DefNode =>
        val result = balanceBlock(Block(Seq(node)))
        if (result.stmts.size == 1) result.stmts.head else result
      case other =>
        val result = balanceBlock(Block(Seq(other)))
        if (result.stmts.size == 1) result.stmts.head else result
    }

    def balanceBlock(block: Block): Block = {
      val statements = block.stmts.flatMap(flattenBlocks)

      // LowFormOptimized can inline the last operation into a connect or another
      // sink. Name such roots only when their tree is actually rewritten. A
      // Conditionally is a separate scope and is handled recursively below.
      val statementRoots = new java.util.IdentityHashMap[Statement, Seq[(Expression, DefNode)]]
      val sinkNodes = mutable.ArrayBuffer.empty[DefNode]
      statements.filterNot(s => s.isInstanceOf[DefNode] || s.isInstanceOf[Conditionally]).foreach { s =>
        val roots = mutable.ArrayBuffer.empty[(Expression, DefNode)]
        s.mapExpr { e =>
          e match {
            case p: DoPrim if eligible(p) =>
              val n = DefNode(NoInfo, namespace.newName("__rteaal_balance_root"), p)
              roots += e -> n
              sinkNodes += n
            case _ =>
          }
          e
        }
        if (roots.nonEmpty) statementRoots.put(s, roots.toVector)
      }

      val localNodes = statements.collect { case n: DefNode => n }
      val allNodes = localNodes ++ sinkNodes
      val definitions = allNodes.map(n => n.name -> n).toMap
      val candidates = allNodes.collect { case n @ DefNode(_, _, p: DoPrim) if eligible(p) => n }

      val uses = mutable.HashMap.empty[String, Int].withDefaultValue(0)
      def count(e: Expression): Expression = {
        e match { case r: Reference => uses(r.name) += 1; case _ => }
        e.mapExpr(count)
        e
      }
      // Count uses in the whole block, including nested conditional branches.
      // A node used in a branch must not be consumed by a tree in this scope.
      def countStatement(statement: Statement): Unit = statement match {
        case block: Block => block.stmts.foreach(countStatement)
        case conditional: Conditionally =>
          count(conditional.pred)
          countStatement(conditional.conseq)
          countStatement(conditional.alt)
        case other => other.mapExpr(count)
      }
      statements.foreach(countStatement)

      // Estimate arrival depth through local combinational definitions.
      // Extensions and casts are aliases in this model; state, module interfaces
      // and values defined in an enclosing scope are leaves.
      val arrivals = mutable.HashMap.empty[String, Int]
      def exprDepth(e: Expression, lookup: String => Int): Int = e match {
        case r: Reference => lookup(r.name)
        case _ =>
          var childDepth = 0
          e.mapExpr { child => childDepth = childDepth.max(exprDepth(child, lookup)); child }
          val cost = e match {
            case DoPrim(Pad | AsUInt | AsSInt, _, _, _) => 0
            case _: Literal | _: SubField | _: SubIndex => 0
            case _ => 1
          }
          childDepth + cost
      }
      def references(e: Expression): Seq[String] = {
        val found = mutable.ArrayBuffer.empty[String]
        def visit(x: Expression): Expression = {
          x match { case r: Reference if definitions.contains(r.name) => found += r.name; case _ => }
          x.mapExpr(visit)
          x
        }
        visit(e)
        found.toVector
      }
      def arrival(e: Expression): Int = {
        // An explicit stack also handles chains with thousands of named operators.
        var pending = references(e).map(_ -> false).toList
        val visiting = mutable.HashSet.empty[String]
        while (pending.nonEmpty) {
          val (name, ready) = pending.head
          pending = pending.tail
          if (!arrivals.contains(name)) {
            if (ready) {
              arrivals(name) = exprDepth(definitions(name).value, n => arrivals.getOrElse(n, 0))
              visiting -= name
            } else {
              require(visiting.add(name), s"Combinational cycle at ${m.name}.$name")
              pending = references(definitions(name).value).map(_ -> false).toList :::
                ((name -> true) :: pending)
            }
          }
        }
        exprDepth(e, n => arrivals.getOrElse(n, 0))
      }

      // Resolve only single-use nodes, aliases, and lossless extensions leading to
      // the same operator. A failed lookup leaves the entire operand untouched.
      def expand(e: Expression, root: DoPrim): Option[(DoPrim, Vector[String])] = {
        var current = e
        val names = mutable.ArrayBuffer.empty[String]
        val seen = mutable.HashSet.empty[String]
        while (true) current match {
          case r: Reference if uses(r.name) == 1 && !protectedNames(r.name) &&
              definitions.contains(r.name) && seen.add(r.name) =>
            names += r.name
            current = definitions(r.name).value
          case p: DoPrim if p.op == Pad && root.op != Cat && p.args.size == 1 &&
              p.consts.size == 1 && family(p.tpe) == family(root.tpe) &&
              family(p.args.head.tpe) == family(root.tpe) &&
              width(p.tpe) == width(p.args.head.tpe).max(p.consts.head) =>
            current = p.args.head
          case p: DoPrim if p.op == root.op && family(p.tpe) == family(root.tpe) && eligible(p) =>
            return Some(p -> names.toVector)
          case _ => return None
        }
        None
      }

      // Find maximal trees without relying on declaration order or scanning every
      // prefix of a long chain. Shared values start independent trees.
      val hasParent = mutable.HashSet.empty[String]
      candidates.foreach { n =>
        val root = n.value.asInstanceOf[DoPrim]
        var pending = root.args.toList
        while (pending.nonEmpty) {
          val e = pending.head
          pending = pending.tail
          expand(e, root).foreach { case (p, names) =>
            if (names.nonEmpty) hasParent ++= names
            else pending = p.args.toList ::: pending
          }
        }
      }
      val removed = mutable.HashSet.empty[String]
      val replacements = mutable.HashMap.empty[String, Seq[Statement]]
      candidates.filterNot(n => hasParent(n.name)).foreach { n =>
        val root = n.value.asInstanceOf[DoPrim]
        val leaves = mutable.ArrayBuffer.empty[Expression]
        val consumed = mutable.HashSet.empty[String]
        var oldDepth = 0
        var pending = List((root: Expression) -> 0)
        while (pending.nonEmpty) {
          val (e, depth) = pending.head
          pending = pending.tail
          expand(e, root) match {
            case Some((p, names)) =>
              consumed ++= names
              pending = p.args.map(_ -> (depth + 1)).toList ::: pending
            case None =>
              leaves += e
              oldDepth = oldDepth.max(depth)
          }
        }
        val balancedDepth = if (leaves.size <= 1) 0
          else 32 - Integer.numberOfLeadingZeros(leaves.size - 1)
        if (leaves.size >= 4 && oldDepth > balancedDepth) {
          val before = arrival(root)
          val generated = mutable.ArrayBuffer.empty[Statement]
          def emit(e: Expression): Expression = {
            val name = namespace.newName("__rteaal_balance")
            generated += DefNode(n.info, name, e)
            WRef(name, e.tpe, NodeKind, SourceFlow)
          }
          def pad(e: Expression, w: BigInt): Expression = {
            if (width(e.tpe) == w) e
            else emit(DoPrim(Pad, Seq(e), Seq(w), e.tpe.mapWidth(_ => IntWidth(w))))
          }
          def tree(start: Int, end: Int, top: Boolean = false): Expression = {
            if (end - start == 1) return leaves(start)
            val mid = start + (end - start) / 2
            val a = tree(start, mid)
            val b = tree(mid, end)
            // Preserve the extractor's equal-width add/bitwise operand contract.
            val args = root.op match {
              case Add | And | Or | Xor =>
                val w = width(a.tpe).max(width(b.tpe))
                Seq(pad(a, w), pad(b, w))
              case _ => Seq(a, b)
            }
            val p = DoPrim(root.op, args, Seq.empty, resultType(root.op, args(0).tpe, args(1).tpe))
            if (!top) emit(p)
            else {
              // Keep the root's public type, including its original extension bits.
              val fitted = if (p.tpe == root.tpe) p else {
                val raw = emit(p)
                if (width(p.tpe) < width(root.tpe))
                  DoPrim(Pad, Seq(raw), Seq(width(root.tpe)), root.tpe)
                else {
                  val bits = DoPrim(Bits, Seq(raw), Seq(width(root.tpe) - 1, BigInt(0)),
                    UIntType(IntWidth(width(root.tpe))))
                  if (family(root.tpe) == 1) DoPrim(AsSInt, Seq(emit(bits)), Seq.empty, root.tpe)
                  else bits
                }
              }
              generated += n.copy(value = fitted)
              WRef(n.name, root.tpe, NodeKind, SourceFlow)
            }
          }
          tree(0, leaves.size, top = true)
          val newArrivals = mutable.HashMap.empty[String, Int]
          generated.foreach { case d: DefNode =>
            newArrivals(d.name) = exprDepth(d.value,
              name => newArrivals.getOrElse(name, arrivals.getOrElse(name, 0)))
          }
          if (newArrivals(n.name) < before) {
            removed ++= consumed
            replacements(n.name) = generated.toVector
          }
        }
      }

      def rewrite(statement: Statement): Seq[Statement] = statement match {
        case block: Block => Seq(balanceBlock(block))
        case d: DefNode if replacements.contains(d.name) => replacements(d.name)
        case d: DefNode if removed(d.name) => Seq.empty
        case conditional: Conditionally => Seq(conditional.copy(
          conseq = balanceStatement(conditional.conseq),
          alt = balanceStatement(conditional.alt)))
        case x if statementRoots.containsKey(x) =>
          val roots = statementRoots.get(x).filter { case (_, n) => replacements.contains(n.name) }
          val refs = new java.util.IdentityHashMap[Expression, Expression]
          roots.foreach { case (e, n) => refs.put(e, WRef(n.name, e.tpe, NodeKind, SourceFlow)) }
          roots.flatMap { case (_, n) => replacements(n.name) } :+
            x.mapExpr(e => if (refs.containsKey(e)) refs.get(e) else e)
        case x => Seq(x)
      }
      block.copy(stmts = statements.flatMap(rewrite))
    }

    balanceStatement(m.body) match {
      case block: Block => m.copy(body = block)
      case other => m.copy(body = other)
    }
  }

  private def enabled: Boolean = !sys.props.get("rteaal.balanceAssociative").contains("false")

  private def balance(c: Circuit, protectedNames: Map[String, Set[String]]): Circuit = {
    if (!enabled) c
    else c.mapModule {
      case m: Module => balanceModule(m, protectedNames.getOrElse(m.name, Set.empty))
      case x => x
    }
  }

  override def run(c: Circuit): Circuit = balance(c, Map.empty)

  override def execute(state: CircuitState): CircuitState = {
    val protectedNames = state.annotations.collect { case DontTouchAnnotation(t) => t.module -> t.ref }
      .groupMap(_._1)(_._2).map { case (module, names) => module -> names.toSet }
    state.copy(circuit = balance(state.circuit, protectedNames))
  }
}
