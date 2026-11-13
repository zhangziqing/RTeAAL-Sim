package essent

import essent.passes.NormalizeMuxIndex
import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable

class NormalizeMuxIndexTest extends AnyFlatSpec {
  private val bit = UIntType(IntWidth(1))
  private val stateType = UIntType(IntWidth(8))

  private case class Fixture(circuit: Circuit, rowWidth: Int, colWidth: Int, codes: Seq[Int]) {
    val entries: Int = 1 << (rowWidth + colWidth)
  }

  private def statements(statement: Statement): Seq[Statement] = statement match {
    case block: Block => block.stmts.flatMap(statements)
    case other => Seq(other)
  }

  private def fixture(rowWidth: Int, colWidth: Int, codes: Seq[Int]): Fixture = {
    val rowType = UIntType(IntWidth(rowWidth))
    val colType = UIntType(IntWidth(colWidth))
    val entries = 1 << (rowWidth + colWidth)
    val ports = Seq(
      Port(NoInfo, "row", Input, rowType),
      Port(NoInfo, "col", Input, colType)) ++
      (0 until entries).map(i => Port(NoInfo, s"state_$i", Input, stateType)) ++
      Seq(Port(NoInfo, "table_out", Output, stateType),
        Port(NoInfo, "condition_probe", Output, bit),
        Port(NoInfo, "shared_eq_probe", Output, bit))

    val nodes = mutable.ArrayBuffer.empty[Statement]
    val rowRefs = (0 until (1 << rowWidth)).map { value =>
      val name = s"row_eq_$value"
      val literal = UIntLiteral(value, IntWidth(rowWidth))
      val args = if ((value & 1) == 0)
        Seq(WRef("row", rowType, PortKind, SourceFlow), literal)
      else Seq(literal, WRef("row", rowType, PortKind, SourceFlow))
      nodes += DefNode(NoInfo, name, DoPrim(Eq, args, Seq.empty, bit))
      WRef(name, bit, NodeKind, SourceFlow)
    }
    val colRefs = (0 until (1 << colWidth)).map { value =>
      val name = s"col_eq_$value"
      val literal = UIntLiteral(value, IntWidth(colWidth))
      val args = if ((value & 1) == 0)
        Seq(WRef("col", colType, PortKind, SourceFlow), literal)
      else Seq(literal, WRef("col", colType, PortKind, SourceFlow))
      nodes += DefNode(NoInfo, name, DoPrim(Eq, args, Seq.empty, bit))
      WRef(name, bit, NodeKind, SourceFlow)
    }

    var selected: Expression = WRef("state_0", stateType, PortKind, SourceFlow)
    codes.zipWithIndex.foreach { case (code, position) =>
      val row = code >> colWidth
      val col = code & ((1 << colWidth) - 1)
      val pair = if ((position & 1) == 0) Seq(rowRefs(row), colRefs(col))
        else Seq(colRefs(col), rowRefs(row))
      val conditionName = s"condition_$position"
      nodes += DefNode(NoInfo, conditionName, DoPrim(And, pair, Seq.empty, bit))
      val muxName = s"mux_$position"
      val mux = Mux(WRef(conditionName, bit, NodeKind, SourceFlow),
        WRef(s"state_$code", stateType, PortKind, SourceFlow), selected, stateType)
      nodes += DefNode(NoInfo, muxName, mux)
      selected = WRef(muxName, stateType, NodeKind, SourceFlow)
    }

    val observed = if (codes.contains(1)) WRef(s"condition_${codes.indexOf(1)}", bit,
      NodeKind, SourceFlow) else UIntLiteral(0, IntWidth(1))
    nodes += Connect(NoInfo, WRef("table_out", stateType, PortKind, SinkFlow), selected)
    nodes += Connect(NoInfo, WRef("condition_probe", bit, PortKind, SinkFlow), observed)
    nodes += Connect(NoInfo, WRef("shared_eq_probe", bit, PortKind, SinkFlow), rowRefs(0))
    Fixture(Circuit(NoInfo, Seq(Module(NoInfo, "MuxIndexProbe", ports, Block(nodes.toVector))),
      "MuxIndexProbe"), rowWidth, colWidth, codes)
  }

  private def evaluate(circuit: Circuit, row: Int, col: Int, data: Seq[Int]): Map[String, BigInt] = {
    val values = mutable.HashMap[String, BigInt]("row" -> BigInt(row), "col" -> BigInt(col))
    data.zipWithIndex.foreach { case (value, i) => values(s"state_$i") = BigInt(value) }

    def eval(expression: Expression): BigInt = expression match {
      case reference: Reference => values(reference.name)
      case literal: UIntLiteral => literal.value
      case primitive: DoPrim =>
        val args = primitive.args.map(eval)
        primitive.op match {
          case Eq => if (args(0) == args(1)) BigInt(1) else BigInt(0)
          case And => args(0) & args(1)
          case Cat => (args(0) << bitWidth(primitive.args(1).tpe).toInt) | args(1)
          case other => fail(s"Unexpected operation in test fixture: $other")
        }
      case mux: Mux => if (eval(mux.cond) != 0) eval(mux.tval) else eval(mux.fval)
      case other => fail(s"Unexpected expression in test fixture: $other")
    }

    statements(circuit.modules.head.asInstanceOf[Module].body).foreach {
      case node: DefNode => values(node.name) = eval(node.value)
      case Connect(_, reference: Reference, expression) => values(reference.name) = eval(expression)
      case _ =>
    }
    values.toMap
  }

  private def normalized(circuit: Circuit): Circuit = NormalizeMuxIndex.run(circuit)

  "NormalizeMuxIndex" should "normalize a 64 by 16 table while preserving all values and its default" in {
    val input = fixture(6, 4, 1 until 1024)
    val result = normalized(input.circuit)
    val rewritten = statements(result.modules.head.asInstanceOf[Module].body)
    val cats = rewritten.collect {
      case DefNode(_, _, primitive: DoPrim) if primitive.op == Cat => primitive
    }
    assert(cats.size == 1)
    assert(cats.head.args.map(_.serialize) == Seq("row", "col"))
    assert(rewritten.collect { case DefNode(_, _, _: Mux) => 1 }.size == 1023)
    assert(rewritten.collect {
      case DefNode(_, _, primitive: DoPrim) if primitive.op == And => primitive
    }.isEmpty)
    assert(rewritten.collect {
      case DefNode(_, _, primitive: DoPrim) if primitive.op == Eq &&
          primitive.args.head.isInstanceOf[WRef] &&
          primitive.args.head.asInstanceOf[WRef].name.startsWith("__rteaal_mux_index") => 1
    }.size == 1023)

    firrtl.passes.CheckTypes.run(result)
    firrtl.passes.CheckWidths.run(result)
    assert(NormalizeMuxIndex.run(result) == result)
    val graph = StatementGraph(result)
    val externalPorts = Extract.findExternalPorts(result)
    val unresolved = graph.nodeRange().filter(id => graph.idToStmt(id) == EmptyStmt)
      .map(graph.idToName).filterNot(externalPorts.contains)
    assert(unresolved.isEmpty, s"Unresolved statements after normalization: $unresolved")
    new Renamer().populateFromSG(graph, externalPorts)

    for (round <- 0 until 2; row <- 0 until 64; col <- 0 until 16) {
      val data = (0 until 1024).map(i => (i * 37 + round * 61 + (i >> 3)) & 0xff)
      val observed = evaluate(input.circuit, row, col, data)
      val actual = evaluate(result, row, col, data)
      val index = (row << 4) | col
      assert(actual("table_out") == BigInt(data(index)), s"round=$round index=$index")
      assert(actual("table_out") == observed("table_out"), s"round=$round index=$index")
      assert(actual("condition_probe") == (if (row == 0 && col == 1) 1 else 0))
      assert(actual("condition_probe") == observed("condition_probe"))
      assert(actual("shared_eq_probe") == (if (row == 0) 1 else 0))
      assert(actual("shared_eq_probe") == observed("shared_eq_probe"))
    }
  }

  it should "leave sparse and repeated conditions unchanged" in {
    val sparse = fixture(2, 2, Seq(1, 3))
    val repeated = fixture(2, 2, Seq(1, 1, 2))
    assert(NormalizeMuxIndex.run(sparse.circuit) == sparse.circuit)
    assert(NormalizeMuxIndex.run(repeated.circuit) == repeated.circuit)
  }
}
