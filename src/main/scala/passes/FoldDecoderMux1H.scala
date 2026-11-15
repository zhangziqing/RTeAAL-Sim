package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.passes.Pass

import scala.collection.mutable

/** Fold Mux1H(UIntToOH(sel), data) into an eq(sel, i) case chain.
  *
  * The existing mux-chain lookup extraction then replaces the case chain with
  * one binary-indexed chain table, removing the decoder, the one-hot vector and
  * the n-way mux. Only combinational UIntToOH decoders are folded here; a
  * registered decoder would need a same-stage binary address and is left
  * unchanged for now.
  */
object FoldDecoderMux1H extends Pass {
  override def prerequisites = Seq.empty
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  case class Stats(compositions: Int = 0, entries: Int = 0, decoderBits: Int = 0,
      skippedWide: Int = 0, skippedData: Int = 0, skippedStage: Int = 0) {
    def +(other: Stats): Stats = Stats(compositions + other.compositions,
      entries + other.entries, decoderBits + other.decoderBits,
      skippedWide + other.skippedWide, skippedData + other.skippedData,
      skippedStage + other.skippedStage)
  }

  private val bit = UIntType(IntWidth(1))
  private val maxTableEntries = 1024

  // First-prototype scope: the generated combinational read table modules.
  // Widening this needs the same graph-cycle analysis as the full audit.
  private def targetModule(name: String): Boolean =
    name.startsWith("NegedgeDataModule_")

  private def mapModule(module: Module): (Module, Stats) = {
    if (!targetModule(module.name)) return module -> Stats()
    val definitions = mutable.HashMap.empty[String, Expression]
    def collect(statement: Statement): Unit = statement match {
      case block: Block => block.stmts.foreach(collect)
      case node: DefNode => definitions(node.name) = node.value
      case conditional: Conditionally =>
        collect(conditional.conseq)
        collect(conditional.alt)
      case _ =>
    }
    collect(module.body)

    var stats = Stats()
    var debugTableFails = 0

    def resolve(expression: Expression): Expression = {
      var current = expression
      val seen = mutable.HashSet.empty[String]
      var done = false
      while (!done) current match {
        case reference: WRef if definitions.contains(reference.name) &&
            seen.add(reference.name) =>
          current = definitions(reference.name)
        case _ => done = true
      }
      current
    }
    def width(expression: Expression): Int = expression.tpe match {
      case UIntType(IntWidth(value)) if value.isValidInt => value.toInt
      case _ => 0
    }
    def isOneBit(expression: Expression): Boolean = width(expression) == 1
    def isZero(expression: Expression): Boolean = resolve(expression) match {
      case UIntLiteral(value, _) => value == 0
      case _ => false
    }
    def isOne(expression: Expression): Boolean = resolve(expression) match {
      case UIntLiteral(value, _) => value == 1
      case _ => false
    }
    def isAllOnes(expression: Expression, width: Int): Boolean = resolve(expression) match {
      case UIntLiteral(value, _) => value == ((BigInt(1) << width) - 1)
      case _ => false
    }
    def orLeaves(expression: Expression): Seq[Expression] = resolve(expression) match {
      case DoPrim(Or, values, _, _) if values.size >= 2 => values.flatMap(orLeaves)
      case other => Seq(other)
    }
    def bitOf(expression: Expression): Option[(Expression, Int)] = resolve(expression) match {
      case DoPrim(Bits, Seq(vector), Seq(high, low), _) if high == low =>
        Some(vector -> high.toInt)
      case _ => None
    }
    def term(expression: Expression): Option[(Expression, Expression)] = resolve(expression) match {
      case Mux(cond, data, zero, _) if isOneBit(cond) && isZero(zero) =>
        Some(cond -> data)
      case DoPrim(And, Seq(a, b), _, _) if isOneBit(a) && width(b) > 1 =>
        Some(a -> b)
      case DoPrim(And, Seq(a, b), _, _) if isOneBit(b) && width(a) > 1 =>
        Some(b -> a)
      case _ => None
    }
    // UIntToOH lowers to dshl(1, sel); n-entry decoders may be truncated with
    // bits(...) or and(mask) to a non-power-of-two width.
    def decoder(expression: Expression): Option[(Expression, Int, Int)] = resolve(expression) match {
      case DoPrim(Dshl, Seq(base, shift), _, _) if isOne(base) && width(shift) > 0 =>
        Some((shift, width(shift), width(expression)))
      case DoPrim(Bits, Seq(inner), Seq(high, low), _) if low == 0 =>
        decoder(inner).map { case (shift, shiftWidth, _) =>
          (shift, shiftWidth, width(expression))
        }
      case DoPrim(And, Seq(inner, mask), _, _) if isAllOnes(mask, width(expression)) =>
        decoder(inner).map { case (shift, shiftWidth, _) =>
          (shift, shiftWidth, width(expression))
        }
      case DoPrim(And, Seq(mask, inner), _, _) if isAllOnes(mask, width(expression)) =>
        decoder(inner).map { case (shift, shiftWidth, _) =>
          (shift, shiftWidth, width(expression))
        }
      case _ => None
    }

    def composition(expression: Expression): Option[Expression] = {
      // A use of a named node is not itself a Mux1H. Folding it again would
      // duplicate the case chain at every consumer; the defining DefNode is
      // rewritten once instead.
      expression match {
        case _: WRef => return None
        case _ =>
      }
      val leaves = orLeaves(expression)
      if (leaves.size < 4) return None
      val parsed = leaves.map(term)
      if (!parsed.forall(_.isDefined)) {
        stats = stats.copy(skippedData = stats.skippedData + 1)
        return None
      }
      val terms = parsed.flatten
      val conditions = terms.map(_._1).map(bitOf)
      if (!conditions.forall(_.isDefined)) {
        stats = stats.copy(skippedData = stats.skippedData + 1)
        return None
      }
      val bits = conditions.flatten
      val vector = bits.head._1
      val vectorKey = resolve(vector).serialize
      if (!bits.forall(pair => resolve(pair._1).serialize == vectorKey)) {
        stats = stats.copy(skippedData = stats.skippedData + 1)
        return None
      }
      if (bits.map(_._2).distinct.size != bits.size) {
        stats = stats.copy(skippedData = stats.skippedData + 1)
        return None
      }
      val n = bits.map(_._2).max + 1
      if (n > maxTableEntries) {
        stats = stats.copy(skippedWide = stats.skippedWide + 1)
        return None
      }
      val dataType = terms.head._2.tpe
      if (!terms.forall(_._2.tpe == dataType)) {
        stats = stats.copy(skippedData = stats.skippedData + 1)
        return None
      }
      val dataWidth = dataType match {
        case UIntType(IntWidth(width)) if width.isValidInt && width > 0 => width.toInt
        case _ =>
          stats = stats.copy(skippedData = stats.skippedData + 1)
          return None
      }
      decoder(vector) match {
        case None =>
          stats = stats.copy(skippedStage = stats.skippedStage + 1)
          None
        case Some((selector, selectorWidth, vectorWidth)) =>
          if (vectorWidth < n || n > (BigInt(1) << selectorWidth)) {
            stats = stats.copy(skippedWide = stats.skippedWide + 1)
            return None
          }
          // Only fold table reads: every selected value must be a
          // constant-indexed cell of one array (possibly a bundle field). This
          // avoids rewriting arbitrary decoder-driven control muxes, whose
          // case chains can expose unrelated combinational graph cycles.
          def cell(expression: Expression): Option[(String, BigInt)] = resolve(expression) match {
            case SubIndex(base, index: Int, _, _) =>
              Some(resolve(base).serialize -> BigInt(index))
            case SubField(inner, name, _, _) =>
              cell(inner).map { case (base, index) => (base + "." + name, index) }
            case reference: WRef =>
              // Chisel lowers Reg(Vec(...)) into one flat register per entry.
              // Recognise the resulting indexed register family, e.g.
              // data_0_ctrl_fpu_rm, data_1_ctrl_fpu_rm, ...
              val name = reference.name
              val numeric = """^(.*?)(\d+)(.*)$""".r.findAllMatchIn(name).toVector
              numeric.lastOption.map { matchValue =>
                (name.take(matchValue.start(2)) + "|" + name.drop(matchValue.end(2)),
                  BigInt(matchValue.group(2)))
              }
            case _ => None
          }
          val cells = terms.map(term => cell(term._2))
          if (!cells.forall(_.isDefined) ||
              cells.flatten.map(_._1).distinct.size != 1 ||
              cells.flatten.map(_._2).distinct.size != terms.size) {
            stats = stats.copy(skippedData = stats.skippedData + 1)
            if (sys.props.contains("rteaal.foldDecoderMux1H.debug") && debugTableFails < 5) {
              debugTableFails += 1
              println(s"DECODER-MUX1H table skip n=$n data=" +
                terms.map { term =>
                  val resolved = resolve(term._2)
                  s"${resolved.getClass.getSimpleName}:${resolved.serialize.take(120)}"
                }.take(5).mkString(" | "))
            }
            return None
          }
          val dataByIndex = terms.zip(bits).map {
            case ((_, data), (_, index)) => index -> data
          }.toMap
          val zero = UIntLiteral(0, IntWidth(dataWidth))
          var tail: Expression = zero
          (0 until n).reverse.foreach { index =>
            val data = dataByIndex.getOrElse(index, zero)
            val condition = DoPrim(Eq,
              Seq(selector, UIntLiteral(index, IntWidth(selectorWidth))), Seq.empty, bit)
            tail = Mux(condition, data, tail, dataType)
          }
          stats = stats.copy(compositions = stats.compositions + 1,
            entries = stats.entries + n, decoderBits = stats.decoderBits + selectorWidth)
          Some(tail)
      }
    }

    def mapExpression(expression: Expression): Expression = composition(expression) match {
      case Some(replacement) => replacement
      case None => expression.mapExpr(mapExpression)
    }
    def mapStatement(statement: Statement): Statement = statement match {
      case block: Block => block.copy(stmts = block.stmts.map(mapStatement))
      case node: DefNode => node.copy(value = mapExpression(node.value))
      case connect: Connect => connect.copy(expr = mapExpression(connect.expr))
      case conditional: Conditionally => conditional.copy(
        pred = mapExpression(conditional.pred),
        conseq = mapStatement(conditional.conseq),
        alt = mapStatement(conditional.alt))
      case other => other.mapStmt(mapStatement)
    }

    if (definitions.isEmpty) module -> stats
    else module.copy(body = mapStatement(module.body)) -> stats
  }

  def executeWithStats(state: CircuitState): (CircuitState, Stats) = {
    if (sys.props.get("rteaal.foldDecoderMux1H").contains("false")) return state -> Stats()
    var total = Stats()
    val circuit = state.circuit.mapModule {
      case module: Module =>
        val (result, stats) = mapModule(module)
        total = total + stats
        result
      case other => other
    }
    state.copy(circuit = circuit) -> total
  }

  override def execute(state: CircuitState): CircuitState = executeWithStats(state)._1
  override def run(circuit: Circuit): Circuit =
    execute(CircuitState(circuit, Seq.empty)).circuit
}
