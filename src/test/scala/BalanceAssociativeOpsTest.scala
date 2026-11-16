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
            case Not => ~args.head
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

  private def withBody(c: Circuit, statements: Seq[Statement]): Circuit =
    c.copy(modules = Seq(c.modules.head.asInstanceOf[Module].copy(body = Block(statements))))

  it should "match exhaustive two-bit inputs including signed overflow boundaries" in {
    for (op <- Seq(And, Or, Xor, Add, Mul, Cat);
         signed <- (if (op == Add || op == Mul) Seq(false, true) else Seq(false))) {
      val original = chain(op, Seq.fill(4)(2), signed)
      val result = BalanceAssociativeOps.run(original)
      for (a <- 0 until 4; b <- 0 until 4; c <- 0 until 4; d <- 0 until 4) {
        val xs = Seq(a, b, c, d).map(BigInt(_))
        val interpreted = xs.map(v => if (signed && v >= 2) v - 4 else v)
        val expected = op match {
          case Add => interpreted.sum
          case Mul => interpreted.product
          case And => xs.reduce(_ & _)
          case Or => xs.reduce(_ | _)
          case Xor => xs.reduce(_ ^ _)
          case Cat => xs.foldLeft(BigInt(0))((v, x) => (v << 2) | x)
        }
        assert(evaluate(original, xs) == expected)
        assert(evaluate(result, xs) == expected)
      }
    }
  }

  it should "preserve shared nodes and count uses in custom state and memory statements" in {
    val original = chain(And, Seq.fill(17)(8))
    val t = UIntType(IntWidth(8))
    val shared = WRef("n2", t, NodeKind, SourceFlow)
    val state = essent.ir.RegUpdate(NoInfo, WRef("state", t, RegKind), shared)
    val memory = essent.ir.MemWrite("memory", "write", UIntLiteral(1, IntWidth(1)),
      UIntLiteral(1, IntWidth(1)), UIntLiteral(0, IntWidth(1)), shared)
    val withObservers = withBody(original, body(original) ++ Seq(state, memory))
    val result = BalanceAssociativeOps.run(withObservers)
    for (name <- Seq("n1", "n2")) {
      assert(body(result).collect { case d: DefNode if d.name == name => d } ==
        body(original).collect { case d: DefNode if d.name == name => d })
    }
    assert(body(result).contains(state) && body(result).contains(memory))
    assert(depth(result, And) < depth(original, And))
    val xs = (0 until 17).map(i => BigInt(255 - i))
    assert(evaluate(original, xs) == evaluate(result, xs))
  }

  it should "respect dontTouch annotations and retain the annotation sequence" in {
    val original = chain(And, Seq.fill(17)(8))
    val annotation = firrtl.transforms.DontTouchAnnotation(
      firrtl.annotations.CircuitTarget("Test").module("Test").ref("n2"))
    val state = CircuitState(original, Seq(annotation))
    val result = BalanceAssociativeOps.execute(state)
    assert(result.annotations == state.annotations)
    assert(body(result.circuit).contains(body(original)(1)))
    assert(depth(result.circuit, And) < depth(original, And))
  }

  it should "stop at intermediate truncations rather than reassociate modular sums" in {
    val original = chain(Add, Seq.fill(8)(2))
    val t = UIntType(IntWidth(2))
    val nodes = mutable.ArrayBuffer.empty[Statement]
    var value: Expression = WRef("x0", t, PortKind, SourceFlow)
    for (i <- 1 until 8) {
      val sum = DoPrim(Add, Seq(value, WRef(s"x$i", t, PortKind, SourceFlow)), Seq.empty,
        UIntType(IntWidth(3)))
      nodes += DefNode(NoInfo, s"sum$i", sum)
      val bits = DoPrim(Bits, Seq(WRef(s"sum$i", sum.tpe, NodeKind, SourceFlow)),
        Seq(BigInt(1), BigInt(0)), t)
      nodes += DefNode(NoInfo, s"clip$i", bits)
      value = WRef(s"clip$i", t, NodeKind, SourceFlow)
    }
    nodes += Connect(NoInfo, WRef("out", t, PortKind, SinkFlow), value)
    val m = original.modules.head.asInstanceOf[Module]
    val clipped = original.copy(modules = Seq(m.copy(
      ports = m.ports.map(p => p.copy(tpe = t)), body = Block(nodes.toVector))))
    assert(BalanceAssociativeOps.run(clipped) == clipped)
    assert(evaluate(clipped, Seq.fill(8)(BigInt(3))) == 0)
  }

  it should "retain non-associative operators, casts, registers, and external modules" in {
    val original = chain(And, Seq.fill(8)(8))
    val t = UIntType(IntWidth(8))
    val extra = Seq(
      DefNode(NoInfo, "subtract", DoPrim(Sub, Seq(WRef("x0", t), WRef("x1", t)),
        Seq.empty, UIntType(IntWidth(9)))),
      DefNode(NoInfo, "cast", DoPrim(AsSInt, Seq(WRef("x0", t)), Seq.empty, SIntType(IntWidth(8)))),
      DefNode(NoInfo, "choose", Mux(UIntLiteral(1, IntWidth(1)), WRef("x0", t), WRef("x1", t), t)),
      DefRegister(NoInfo, "state", t, WRef("clock", ClockType), UIntLiteral(0, IntWidth(1)), WRef("state", t)))
    val ext = ExtModule(NoInfo, "External", Seq.empty, "External", Seq.empty)
    val c = withBody(original, body(original) ++ extra).copy(modules =
      withBody(original, body(original) ++ extra).modules :+ ext)
    val result = BalanceAssociativeOps.run(c)
    extra.foreach(s => assert(body(result).contains(s)))
    assert(result.modules.last == ext)
    val signed = DefNode(NoInfo, "toSigned", DoPrim(AsSInt, Seq(WRef("n2", t)),
      Seq.empty, SIntType(IntWidth(8))))
    val unsigned = DefNode(NoInfo, "toUnsigned", DoPrim(AsUInt, Seq(WRef("toSigned", signed.value.tpe)),
      Seq.empty, t))
    val castBoundary = withBody(original, body(original).take(2) ++ Seq(signed, unsigned) ++ body(original).drop(2).map {
      case n @ DefNode(_, "n3", p: DoPrim) => n.copy(value = p.copy(args = Seq(WRef("toUnsigned", t), p.args(1))))
      case s => s
    })
    val withCasts = BalanceAssociativeOps.run(castBoundary)
    assert(body(withCasts).contains(signed) && body(withCasts).contains(unsigned))
    assert(body(withCasts).contains(body(original)(1)))
    assert(evaluate(withCasts, Seq.fill(8)(BigInt(255))) == 255)
  }

  it should "skip a rewrite when a late input would increase combinational depth" in {
    val original = chain(And, Seq.fill(8)(8))
    val t = UIntType(IntWidth(8))
    var late: Expression = WRef("x7", t, PortKind, SourceFlow)
    val delay = (0 until 16).map { i =>
      val node = DefNode(NoInfo, s"late$i", DoPrim(Not, Seq(late), Seq.empty, t))
      late = WRef(node.name, t, NodeKind, SourceFlow)
      node
    }
    val c = withBody(original, delay ++ body(original).map {
      case n @ DefNode(_, "n7", p: DoPrim) => n.copy(value = p.copy(args = Seq(p.args.head, late)))
      case s => s
    })
    assert(BalanceAssociativeOps.run(c) == c)
  }

  it should "handle forward references and generated-name collisions deterministically" in {
    val original = chain(And, Seq.fill(17)(8))
    val collision = DefNode(NoInfo, "__rteaal_balance", UIntLiteral(0, IntWidth(1)))
    val c = withBody(original, (body(original) :+ collision).reverse)
    val result = BalanceAssociativeOps.run(c)
    val names = body(result).collect { case n: DefNode => n.name }
    assert(names.distinct == names)
    assert(BalanceAssociativeOps.run(c) == result)
    val ordered = withBody(result, StatementGraph(body(result)).stmtsOrdered())
    assert(depth(ordered, And) == 5)
    assert(evaluate(original, Seq.fill(17)(BigInt(171))) ==
      evaluate(ordered, Seq.fill(17)(BigInt(171))))
  }

  it should "validate the rewritten types after the existing Low FIRRTL pipeline" in {
    for (op <- Seq(And, Or, Xor, Add, Mul, Cat); signed <-
         (if (op == Add || op == Mul) Seq(false, true) else Seq(false))) {
      val input = firrtl.Parser.parse(chain(op, Seq.fill(8)(4), signed).serialize)
      val compiler = new firrtl.stage.transforms.Compiler(firrtl.stage.Forms.LowFormOptimized)
      val state = compiler.execute(CircuitState(input, Seq.empty))
      val result = BalanceAssociativeOps.execute(state).circuit
      firrtl.passes.CheckTypes.run(result)
      firrtl.passes.CheckWidths.run(result)
      assert(body(firrtl.passes.InferTypes.run(result)).filterNot(_ == EmptyStmt) ==
        body(result).filterNot(_ == EmptyStmt))
      assert(depth(result, op) == 3)
      val extractor = new TeAALExtractor(mutable.LinkedHashMap.empty)
      StatementGraph(body(result)).stmtsOrdered().foreach(extractor.extractStmt)
      assert(extractor.opInBufferOrder.nonEmpty)
    }
  }

  it should "allow disabling the pass for a reproducible baseline" in {
    val parser = new ArgsParser
    assert(parser.getConfig(Seq("Test.fir")).get.balanceAssociativeOps)
    assert(!parser.getConfig(Seq("Test.fir")).get.normalizeMuxIndex)
    assert(parser.getConfig(Seq("--normalize-mux-index", "Test.fir")).get.normalizeMuxIndex)
    assert(!parser.getConfig(Seq("-O0", "Test.fir")).get.balanceAssociativeOps)
    for (level <- Seq("-O1", "-O2", "-O3", "-O4")) {
      assert(parser.getConfig(Seq(level, "Test.fir")).get.balanceAssociativeOps)
      assert(!parser.getConfig(Seq(level, "--no-associative-balance", "Test.fir")).get.balanceAssociativeOps)
    }
    val previous = sys.props.get("rteaal.balanceAssociative")
    try {
      sys.props("rteaal.balanceAssociative") = "false"
      val c = chain(And, Seq.fill(17)(8))
      assert(BalanceAssociativeOps.execute(CircuitState(c, Seq.empty)).circuit == c)
      assert(BalanceAssociativeOps.run(c) == c)
    } finally {
      previous match {
        case Some(value) => sys.props("rteaal.balanceAssociative") = value
        case None => sys.props.remove("rteaal.balanceAssociative")
      }
    }
  }
}
