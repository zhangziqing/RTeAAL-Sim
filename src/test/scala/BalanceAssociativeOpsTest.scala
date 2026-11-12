package essent

import essent.passes.BalanceAssociativeOps
import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable

class BalanceAssociativeOpsTest extends AnyFlatSpec {
  private def width(t: Type): Int = bitWidth(t).toInt
  private def mask(w: Int): BigInt = (BigInt(1) << w) - 1
  private def stmts(s: Statement): Seq[Statement] = s match {
    case b: Block => b.stmts.flatMap(stmts)
    case x => Seq(x)
  }
  private def body(c: Circuit): Seq[Statement] = stmts(c.modules.head.asInstanceOf[Module].body)
  private def chain(op: PrimOp, widths: Seq[Int], signed: Boolean = false): Circuit = {
    def tpe(w: Int): Type = if (signed) SIntType(IntWidth(w)) else UIntType(IntWidth(w))
    val inputs = widths.zipWithIndex.map { case (w, i) => Port(NoInfo, s"x$i", Input, tpe(w)) }
    val nodes = mutable.ArrayBuffer.empty[Statement]
    var value: Expression = WRef("x0", inputs.head.tpe, PortKind, SourceFlow)
    widths.indices.drop(1).foreach { i =>
      val rhs = WRef(s"x$i", inputs(i).tpe, PortKind, SourceFlow)
      val w = op match {
        case Add => width(value.tpe).max(width(rhs.tpe)) + 1
        case Mul | Cat => width(value.tpe) + width(rhs.tpe)
        case _ => width(value.tpe).max(width(rhs.tpe))
      }
      val p = DoPrim(op, Seq(value, rhs), Seq.empty, tpe(w))
      nodes += DefNode(NoInfo, s"n$i", p)
      value = WRef(s"n$i", p.tpe, NodeKind, SourceFlow)
    }
    val output = Port(NoInfo, "out", Output, value.tpe)
    nodes += Connect(NoInfo, WRef("out", value.tpe, PortKind, SinkFlow), value)
    Circuit(NoInfo, Seq(Module(NoInfo, "Test", inputs :+ output, Block(nodes.toVector))), "Test")
  }

  // Evaluate integer values independently, normalizing every expression to its
  // declared bit width and two's-complement signedness.
  private def evaluate(c: Circuit, inputs: Seq[BigInt]): BigInt = {
    val values = mutable.HashMap.from(inputs.zipWithIndex.map { case (v, i) => s"x$i" -> v })
    def eval(e: Expression): BigInt = {
      val raw = e match {
        case r: Reference => values(r.name)
        case l: UIntLiteral => l.value
        case l: SIntLiteral => l.value
        case p: DoPrim =>
          val args = p.args.map(eval)
          p.op match {
            case Add => args(0) + args(1)
            case Mul => args(0) * args(1)
            case And => args(0) & args(1)
            case Or => args(0) | args(1)
            case Xor => args(0) ^ args(1)
            case Cat => (args(0) << width(p.args(1).tpe)) | args(1)
            case Pad | AsSInt | AsUInt => args.head
            case Bits => (args.head >> p.consts(1).toInt) & mask(width(p.tpe))
          }
      }
      val bits = raw & mask(width(e.tpe))
      e.tpe match {
        case _: SIntType if bits.testBit(width(e.tpe) - 1) => bits - (BigInt(1) << width(e.tpe))
        case _ => bits
      }
    }
    body(c).foreach {
      case n: DefNode => values(n.name) = eval(n.value)
      case Connect(_, r: Reference, e) => values(r.name) = eval(e)
      case _ =>
    }
    values("out")
  }

  private def depth(c: Circuit, op: PrimOp): Int = {
    val depths = mutable.HashMap.empty[String, Int].withDefaultValue(0)
    def d(e: Expression): Int = e match {
      case r: Reference => depths(r.name)
      case p: DoPrim => p.args.map(d).max + (if (p.op == op) 1 else 0)
      case _ => 0
    }
    body(c).foreach {
      case n: DefNode => depths(n.name) = d(n.value)
      case Connect(_, r: Reference, e) => depths(r.name) = d(e)
      case _ =>
    }
    depths("out")
  }

  "BalanceAssociativeOps" should "reduce long and non-power-of-two trees to logarithmic depth" in {
    for (op <- Seq(And, Or, Xor); count <- Seq(4, 5, 17, 1024, 8192)) {
      val original = chain(op, Seq.fill(count)(8))
      val result = BalanceAssociativeOps.run(original)
      assert(depth(original, op) == count - 1)
      assert(depth(result, op) == 32 - Integer.numberOfLeadingZeros(count - 1))
      assert(body(result).count(_.isInstanceOf[DefNode]) == count - 1)
      assert(BalanceAssociativeOps.run(result) == result)
    }
  }

  it should "preserve unsigned and signed arithmetic and concatenation values" in {
    val random = new scala.util.Random(20261113L)
    for (op <- Seq(And, Or, Xor, Add, Mul, Cat);
         signed <- (if (op == Add || op == Mul) Seq(false, true) else Seq(false));
         widths <- Seq(Seq.fill(9)(8), Seq(1, 7, 63, 64, 65, 127, 128, 3, 2))) {
      val original = chain(op, widths, signed)
      val result = BalanceAssociativeOps.run(original)
      assert(depth(result, op) == 4)
      assert(result.modules.head.ports == original.modules.head.ports)
      val samples = Seq(Seq.fill(widths.size)(BigInt(0)), widths.map(w => mask(w)),
        widths.map(w => BigInt(1) << (w - 1))) ++
        Seq.fill(64)(widths.map(w => BigInt(w, random)))
      samples.foreach { xs => assert(evaluate(original, xs) == evaluate(result, xs), s"$op $signed $xs") }
    }
  }

  it should "leave already balanced and short expressions unchanged" in {
    for (op <- Seq(And, Or, Xor, Add, Mul, Cat); count <- Seq(2, 3)) {
      val original = chain(op, Seq.fill(count)(8))
      assert(BalanceAssociativeOps.run(original) == original)
    }
  }

  it should "retain every generated statement when the module body is a single node" in {
    val t = UIntType(IntWidth(1))
    val value = (1 until 8).foldLeft[Expression](UIntLiteral(1, IntWidth(1))) { (a, _) =>
      DoPrim(And, Seq(a, UIntLiteral(1, IntWidth(1))), Seq.empty, t)
    }
    val c = Circuit(NoInfo, Seq(Module(NoInfo, "Test", Seq.empty, DefNode(NoInfo, "root", value))), "Test")
    val result = body(BalanceAssociativeOps.run(c))
    assert(result.count(_.isInstanceOf[DefNode]) == 7)
    assert(result.last.asInstanceOf[DefNode].name == "root")
  }
}
