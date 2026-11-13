package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.passes.Pass
import firrtl.transforms.DontTouchAnnotation

import scala.collection.mutable

/** Fold two-dimensional equality selectors into one dense lookup index. */
object NormalizeMuxIndex extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  case class Stats(chains: Int = 0, muxes: Int = 0)
  private case class IndexKey(row: Expression, col: Expression, rowWidth: Int, colWidth: Int)
  private case class EqInfo(selector: Expression, value: BigInt, nodeName: Option[String])
  private case class ConditionInfo(
      first: EqInfo,
      second: EqInfo,
      andNode: Option[String],
      eqNodes: Set[String])
  private case class ChainPlan(
      muxes: Vector[(String, Mux)],
      index: IndexKey,
      codes: Vector[(String, BigInt, Option[String])],
      oldEqNodes: Set[String])

  private def knownUIntWidth(tpe: Type): Option[Int] = tpe match {
    case UIntType(IntWidth(width)) if width > 0 && width <= 16 => Some(width.toInt)
    case _ => None
  }

  private def flattened(statement: Statement): Seq[Statement] = statement match {
    case block: Block => block.stmts.flatMap(flattened)
    case other => Seq(other)
  }

  private def normalizeModule(m: Module, protectedNames: Set[String]): (Module, Stats) = {
    val statements = flattened(m.body)
    val definitions = statements.collect { case node: DefNode => node.name -> node }.toMap
    val muxes = statements.collect {
      case node: DefNode if node.value.isInstanceOf[Mux] => node.name -> node.value.asInstanceOf[Mux]
    }
    if (muxes.isEmpty) return m -> Stats()

    def resolveRoot(expression: Expression, op: PrimOp): (Option[DoPrim], Option[String]) = {
      var current = expression
      var foundName: Option[String] = None
      val seen = mutable.HashSet.empty[String]
      while (current match {
        case reference: WRef if definitions.contains(reference.name) && seen.add(reference.name) =>
          val value = definitions(reference.name).value
          value match {
            case primitive: DoPrim if primitive.op == op =>
              foundName = Some(reference.name)
              current = primitive
            case other => current = other
          }
          true
        case _ => false
      }) {}
      current match {
        case primitive: DoPrim if primitive.op == op => Some(primitive) -> foundName
        case _ => None -> None
      }
    }

    def uintLiteral(expression: Expression): Option[BigInt] = {
      var current = expression
      val seen = mutable.HashSet.empty[String]
      while (current match {
        case reference: WRef if definitions.contains(reference.name) && seen.add(reference.name) =>
          definitions(reference.name).value match {
            case literal: UIntLiteral => current = literal
            case alias: WRef => current = alias
            case _ => return None
          }
          true
        case _ => false
      }) {}
      current match {
        case literal: UIntLiteral => Some(literal.value)
        case _ => None
      }
    }

    def parseEq(expression: Expression): Option[EqInfo] = {
      val (root, nodeName) = resolveRoot(expression, Eq)
      root.flatMap { primitive =>
        if (primitive.args.size != 2 || primitive.consts.nonEmpty) None
        else {
          val leftValue = uintLiteral(primitive.args(0))
          val rightValue = uintLiteral(primitive.args(1))
          (leftValue, rightValue) match {
            case (Some(value), None) => Some(EqInfo(primitive.args(1), value, nodeName))
            case (None, Some(value)) => Some(EqInfo(primitive.args(0), value, nodeName))
            case _ => None
          }
        }
      }
    }

    def parseCondition(expression: Expression): Option[ConditionInfo] = {
      val (andRoot, andNode) = resolveRoot(expression, And)
      andRoot.flatMap { and =>
        if (and.args.size != 2 || and.consts.nonEmpty) None
        else for {
          first <- parseEq(and.args(0))
          second <- parseEq(and.args(1))
          firstWidth <- knownUIntWidth(first.selector.tpe)
          secondWidth <- knownUIntWidth(second.selector.tpe)
          if firstWidth + secondWidth <= 16
          if first.selector != second.selector
          if first.value >= 0 && first.value < (BigInt(1) << firstWidth)
          if second.value >= 0 && second.value < (BigInt(1) << secondWidth)
        } yield ConditionInfo(first, second, andNode,
          Set(first.nodeName, second.nodeName).flatten)
      }
    }

    def muxReference(expression: Expression): Option[(String, Mux)] = {
      var current = expression
      val seen = mutable.HashSet.empty[String]
      while (current match {
        case reference: WRef if definitions.contains(reference.name) && seen.add(reference.name) =>
          definitions(reference.name).value match {
            case mux: Mux => return Some(reference.name -> mux)
            case alias: WRef => current = alias
            case _ => return None
          }
          true
        case _ => false
      }) {}
      None
    }

    val muxNames = muxes.map(_._1).toSet
    val childNames = muxes.flatMap { case (_, mux) => muxReference(mux.fval).map(_._1) }.toSet
    val roots = muxes.filterNot { case (name, _) => childNames(name) }

    def traceChain(root: (String, Mux)): Vector[(String, Mux)] = {
      val result = mutable.ArrayBuffer.empty[(String, Mux)]
      val seen = mutable.HashSet.empty[String]
      var current = Option(root)
      while (current.nonEmpty && seen.add(current.get._1)) {
        val item = current.get
        result += item
        current = muxReference(item._2.fval).filter { case (name, _) => muxNames(name) }
      }
      if (current.nonEmpty) Vector.empty else result.toVector
    }

    val traced = roots.map(traceChain).filter(_.size >= 2)
    val memberships = traced.flatMap(_.map(_._1)).groupMapReduce(identity)(_ => 1)(_ + _)
    val nonOverlapping = traced.filter(_.forall { case (name, _) => memberships(name) == 1 })

    val plans = nonOverlapping.flatMap { chain =>
      val parsed = chain.map { case (name, mux) =>
        parseCondition(mux.cond).map(name -> _)
      }
      if (parsed.exists(_.isEmpty)) None
      else {
        val conditions = parsed.flatten
        val first = conditions.head._2.first
        val second = conditions.head._2.second
        val firstWidth = knownUIntWidth(first.selector.tpe).get
        val secondWidth = knownUIntWidth(second.selector.tpe).get
        val direct = IndexKey(first.selector, second.selector, firstWidth, secondWidth)
        val codes = conditions.map { case (muxName, condition) =>
          val rowCol =
            if (condition.first.selector == direct.row && condition.second.selector == direct.col)
              Some(condition.first.value -> condition.second.value)
            else if (condition.first.selector == direct.col && condition.second.selector == direct.row)
              Some(condition.second.value -> condition.first.value)
            else None
          rowCol.map { case (row, col) =>
            (muxName, (row << secondWidth) | col, condition.andNode)
          }
        }

        if (codes.exists(_.isEmpty)) None
        else {
          val values = codes.flatten.map(_._2)
          val domainSize = BigInt(1) << (firstWidth + secondWidth)
          val dense = values.distinct.size == values.size &&
            (values.size == domainSize || values.size == domainSize - 1)
          if (!dense) None
          else Some(ChainPlan(chain, direct, codes.flatten,
            conditions.flatMap(_._2.eqNodes).toSet))
        }
      }
    }

    if (plans.isEmpty) return m -> Stats()

    val namespace = Namespace(m)
    val indexNodes = mutable.LinkedHashMap.empty[IndexKey, DefNode]
    val andUpdates = mutable.HashMap.empty[String, Expression]
    val muxUpdates = mutable.HashMap.empty[String, Mux]
    val generatedConditions = mutable.ArrayBuffer.empty[DefNode]
    val oldEqNodes = mutable.HashSet.empty[String]

    plans.foreach { plan =>
      val indexNode = indexNodes.getOrElseUpdate(plan.index, {
        val name = namespace.newName("__rteaal_mux_index")
        val tpe = UIntType(IntWidth(plan.index.rowWidth + plan.index.colWidth))
        DefNode(NoInfo, name, DoPrim(Cat, Seq(plan.index.row, plan.index.col), Seq.empty, tpe))
      })
      val indexType = indexNode.value.tpe
      val indexRef = WRef(indexNode.name, indexType, NodeKind, SourceFlow)
      plan.codes.foreach { case (muxName, code, andNode) =>
        val comparison = DoPrim(Eq, Seq(indexRef,
          UIntLiteral(code, indexType.asInstanceOf[UIntType].width)), Seq.empty, UIntType(IntWidth(1)))
        andNode match {
          case Some(name) =>
            andUpdates.get(name) match {
              case Some(existing) => require(existing == comparison, s"Conflicting mux-index rewrite for ${m.name}.$name")
              case None => andUpdates(name) = comparison
            }
          case None =>
            val conditionName = namespace.newName("__rteaal_mux_index_eq")
            generatedConditions += DefNode(NoInfo, conditionName, comparison)
            val mux = plan.muxes.find(_._1 == muxName).get._2
            muxUpdates(muxName) = mux.copy(cond = WRef(conditionName,
              UIntType(IntWidth(1)), NodeKind, SourceFlow))
        }
      }
      oldEqNodes ++= plan.oldEqNodes
    }

    def rewrite(statement: Statement): Statement = statement match {
      case block: Block => block.copy(stmts = block.stmts.map(rewrite))
      case node: DefNode if andUpdates.contains(node.name) => node.copy(value = andUpdates(node.name))
      case node: DefNode if muxUpdates.contains(node.name) => node.copy(value = muxUpdates(node.name))
      case other => other
    }

    val generated = indexNodes.values.toSeq ++ generatedConditions
    val withGenerated = if (generated.isEmpty) rewrite(m.body)
      else Block(generated ++ Seq(rewrite(m.body)))

    val uses = mutable.HashMap.empty[String, Int].withDefaultValue(0)
    def countReferences(expression: Expression): Expression = {
      expression match { case reference: Reference => uses(reference.name) += 1; case _ => }
      expression.mapExpr(countReferences)
      expression
    }
    withGenerated.mapExpr(countReferences)
    val deadEqNodes = oldEqNodes.filter(name =>
      !protectedNames(name) && uses(name) == 0 && definitions.get(name).exists(_.value match {
        case primitive: DoPrim => primitive.op == Eq
        case _ => false
      }))

    def removeDead(statement: Statement): Seq[Statement] = statement match {
      case block: Block => Seq(block.copy(stmts = block.stmts.flatMap(removeDead)))
      case node: DefNode if deadEqNodes(node.name) => Seq.empty
      case other => Seq(other)
    }

    val cleaned = removeDead(withGenerated)
    val body = if (cleaned.size == 1) cleaned.head else Block(cleaned)
    m.copy(body = body) -> Stats(plans.size, plans.map(_.muxes.size).sum)
  }

  private def normalize(circuit: Circuit, protectedNames: Map[String, Set[String]]): (Circuit, Stats) = {
    var total = Stats()
    val modules = circuit.modules.map {
      case module: Module =>
        val (rewritten, stats) = normalizeModule(module, protectedNames.getOrElse(module.name, Set.empty))
        total = Stats(total.chains + stats.chains, total.muxes + stats.muxes)
        rewritten
      case other => other
    }
    circuit.copy(modules = modules) -> total
  }

  def runWithStats(circuit: Circuit): (Circuit, Stats) = normalize(circuit, Map.empty)

  override def run(circuit: Circuit): Circuit = runWithStats(circuit)._1

  def executeWithStats(state: CircuitState): (CircuitState, Stats) = {
    val protectedNames = state.annotations.collect {
      case DontTouchAnnotation(target) => target.module -> target.ref
    }.groupMap(_._1)(_._2).map { case (module, names) => module -> names.toSet }
    val (circuit, stats) = normalize(state.circuit, protectedNames)
    state.copy(circuit = circuit) -> stats
  }

  override def execute(state: CircuitState): CircuitState = executeWithStats(state)._1
}
