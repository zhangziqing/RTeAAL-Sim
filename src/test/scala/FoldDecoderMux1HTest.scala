package essent

import essent.passes.FoldDecoderMux1H
import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable

class FoldDecoderMux1HTest extends AnyFlatSpec {
  private val bit = UIntType(IntWidth(1))
  private val selType = UIntType(IntWidth(2))
  private val dataType = UIntType(IntWidth(8))
  private def ref(name: String, tpe: Type = dataType): Expression =
    WRef(name, tpe, NodeKind, SourceFlow)
  private def zero: Expression = UIntLiteral(0, IntWidth(8))

  private def dataCell(index: Int): Expression =
    SubIndex(ref("data", VectorType(dataType, 4)), index, dataType, SourceFlow)

  private def mux1h(vector: Expression, n: Int): Expression = {
    val terms: Seq[Expression] = (0 until n).map { index =>
      val cond = DoPrim(Bits, Seq(vector), Seq(BigInt(index), BigInt(index)), bit)
      Mux(cond, dataCell(index), zero, dataType)
    }
    terms.reduceLeft((left, right) => DoPrim(Or, Seq(left, right), Seq.empty, dataType))
  }

  private def body(circuit: Circuit): Seq[Statement] =
    circuit.modules.head.asInstanceOf[Module].body.asInstanceOf[Block].stmts

  private def definitions(circuit: Circuit): Map[String, Expression] =
    body(circuit).collect { case node: DefNode => node.name -> node.value }.toMap

  private def evaluate(circuit: Circuit, inputs: Map[String, BigInt]): BigInt = {
    val defs = definitions(circuit)
    val values = mutable.HashMap.from(inputs)
    def eval(expression: Expression): BigInt = expression match {
      case reference: WRef => values.getOrElseUpdate(reference.name, eval(defs(reference.name)))
      case UIntLiteral(value, _) => value
      case Mux(cond, tval, fval, _) => eval(if (eval(cond) != 0) tval else fval)
      case DoPrim(Or, args, _, _) => eval(args(0)) | eval(args(1))
      case DoPrim(Eq, args, _, _) => if (eval(args(0)) == eval(args(1))) 1 else 0
      case DoPrim(Bits, args, consts, _) =>
        (eval(args.head) >> consts(1).toInt) &
          ((BigInt(1) << (consts.head - consts(1) + 1).toInt) - 1)
      case DoPrim(Dshl, args, _, _) => eval(args(0)) << eval(args(1)).toInt
      case SubIndex(base: WRef, index, _, _) => values(s"${base.name}$index")
      case other => sys.error(s"Unexpected expression: $other")
    }
    body(circuit).collectFirst {
      case Connect(_, reference: WRef, expression) if reference.name == "out" => eval(expression)
    }.get
  }

  private def combinational: Circuit = {
    val ports = Seq(Port(NoInfo, "sel", Input, selType),
      Port(NoInfo, "data", Input, VectorType(dataType, 4)), Port(NoInfo, "out", Output, dataType))
    val onehot = DoPrim(Dshl, Seq(UIntLiteral(1, IntWidth(1)), ref("sel", selType)),
      Seq.empty, UIntType(IntWidth(4)))
    Circuit(NoInfo, Seq(Module(NoInfo, "NegedgeDataModule_DecoderMux1HProbe", ports,
      Block(Seq(
        DefNode(NoInfo, "onehot", onehot),
        DefNode(NoInfo, "result", mux1h(onehot, 4)),
        Connect(NoInfo, WRef("out", dataType, PortKind, SinkFlow), ref("result")))))),
      "NegedgeDataModule_DecoderMux1HProbe")
  }

  "FoldDecoderMux1H" should "fold a combinational decoder + Mux1H into an eq case chain" in {
    val original = combinational
    val (state, stats) = FoldDecoderMux1H.executeWithStats(CircuitState(original, Seq.empty))
    assert(stats.compositions == 1 && stats.entries == 4 && stats.decoderBits == 2, stats.toString)
    val result = state.circuit
    firrtl.passes.CheckTypes.run(result)
    firrtl.passes.CheckWidths.run(result)
    assert(definitions(result)("result").toString.contains("eq"))
    for (sel <- 0 until 4; values <- Seq(Seq(1, 2, 3, 4), Seq(255, 0, 128, 7))) {
      val inputs = Map("sel" -> BigInt(sel)) ++ values.zipWithIndex.map { case (value, index) =>
        s"data$index" -> BigInt(value)
      }
      assert(evaluate(original, inputs) == evaluate(result, inputs), s"sel=$sel")
    }
  }

  it should "leave a registered decoder in place" in {
    val registered = Circuit(NoInfo, Seq(Module(NoInfo, "NegedgeDataModule_RegisteredProbe",
      Seq(Port(NoInfo, "sel", Input, selType), Port(NoInfo, "clock", Input, ClockType),
        Port(NoInfo, "data", Input, VectorType(dataType, 4)), Port(NoInfo, "out", Output, dataType)),
      Block(Seq(
        DefRegister(NoInfo, "onehot_reg", UIntType(IntWidth(4)),
          WRef("clock", ClockType, PortKind, SourceFlow),
          UIntLiteral(0, IntWidth(1)), UIntLiteral(0, IntWidth(4))),
        Connect(NoInfo, WRef("onehot_reg", UIntType(IntWidth(4)), NodeKind, SinkFlow),
          DoPrim(Dshl, Seq(UIntLiteral(1, IntWidth(1)), ref("sel", selType)),
            Seq.empty, UIntType(IntWidth(4)))),
        DefNode(NoInfo, "result", mux1h(ref("onehot_reg", UIntType(IntWidth(4))), 4)),
        Connect(NoInfo, WRef("out", dataType, PortKind, SinkFlow), ref("result")))))),
      "NegedgeDataModule_RegisteredProbe")
    val (state, stats) = FoldDecoderMux1H.executeWithStats(CircuitState(registered, Seq.empty))
    assert(stats.compositions == 0 && stats.skippedStage == 1, stats.toString)
    assert(state.circuit == registered)
  }
}
