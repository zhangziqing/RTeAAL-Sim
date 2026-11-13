package essent

import essent.passes.{BalanceAssociativeOps, ReduceConstantMuxChains}
import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable

class ReduceConstantMuxChainsTest extends AnyFlatSpec {
  private val bit = UIntType(IntWidth(1))
  private def body(c: Circuit): Seq[Statement] = c.modules.head.asInstanceOf[Module].body match {
    case b: Block => b.stmts
    case s => Seq(s)
  }
  private def withBody(c: Circuit, ss: Seq[Statement]): Circuit =
    c.copy(modules = Seq(c.modules.head.asInstanceOf[Module].copy(body = Block(ss))))
  private def fixture(codes: Seq[Int], width: Int = 4, hit: Int = 0,
      inline: Boolean = false): Circuit = {
    val tpe = UIntType(IntWidth(width))
    val ports = Seq(Port(NoInfo, "addr", Input, tpe), Port(NoInfo, "other", Input, tpe),
      Port(NoInfo, "out", Output, bit), Port(NoInfo, "probe", Output, bit))
    val nodes = mutable.ArrayBuffer.empty[Statement]
    var previous: Expression = UIntLiteral(1 - hit, IntWidth(1))
    codes.zipWithIndex.foreach { case (value, i) =>
      val constant = UIntLiteral(value, IntWidth(BigInt(value).bitLength.max(1) + i % 2))
      val addr = WRef("addr", tpe, PortKind, SourceFlow)
      val args = if (i % 2 == 0) Seq(addr, constant) else Seq(constant, addr)
      nodes += DefNode(NoInfo, s"cmp_$i", DoPrim(Eq, args, Seq.empty, bit))
      val mux = Mux(WRef(s"cmp_$i", bit, NodeKind, SourceFlow),
        UIntLiteral(hit, IntWidth(1)), previous, bit)
      if (!inline) nodes += DefNode(NoInfo, s"chain_$i", mux)
      previous = if (inline) mux else WRef(s"chain_$i", bit, NodeKind, SourceFlow)
    }
    nodes += Connect(NoInfo, WRef("out", bit, PortKind, SinkFlow), previous)
    nodes += Connect(NoInfo, WRef("probe", bit, PortKind, SinkFlow), WRef("cmp_0", bit))
    Circuit(NoInfo, Seq(Module(NoInfo, "CaseProbe", ports, Block(nodes.toVector))), "CaseProbe")
  }
  private def evaluate(c: Circuit, addr: Int, other: Int = 0): Map[String, BigInt] = {
    val values = mutable.HashMap[String, BigInt]("addr" -> BigInt(addr), "other" -> BigInt(other))
    def eval(e: Expression): BigInt = e match {
      case r: Reference => values(r.name)
      case l: UIntLiteral => l.value
      case Mux(cond, t, f, _) => if (eval(cond) != 0) eval(t) else eval(f)
      case DoPrim(Eq, args, _, _) => if (eval(args(0)) == eval(args(1))) BigInt(1) else BigInt(0)
      case DoPrim(Or, args, _, _) => eval(args(0)) | eval(args(1))
      case DoPrim(Not, args, _, _) => BigInt(1) ^ eval(args.head)
      case x => fail(s"Unexpected test expression: $x")
    }
    body(c).foreach {
      case n: DefNode => values(n.name) = eval(n.value)
      case Connect(_, r: Reference, e) => values(r.name) = eval(e)
      case _ =>
    }
    values.toMap
  }
  private def depth(c: Circuit, mux: Boolean = false): Int = {
    val depths = mutable.HashMap.empty[String, Int].withDefaultValue(0)
    def d(e: Expression): Int = e match {
      case r: Reference => depths(r.name)
      case m: Mux => Seq(m.cond, m.tval, m.fval).map(d).max + (if (mux) 1 else 0)
      case p: DoPrim => p.args.map(d).max + (if (!mux && p.op == Or) 1 else 0)
      case _ => 0
    }
    body(c).foreach {
      case n: DefNode => depths(n.name) = d(n.value)
      case Connect(_, r: Reference, e) => depths(r.name) = d(e)
      case _ =>
    }
    depths("out")
  }
  private def reduce(c: Circuit): Circuit = BalanceAssociativeOps.run(ReduceConstantMuxChains.run(c))

  "ReduceConstantMuxChains" should "preserve both Boolean polarities for every small-width address" in {
    for (width <- 3 to 5; hit <- 0 to 1; inline <- Seq(false, true)) {
      val codes = (0 until 8) ++ Seq(8, 8, 31, 32)
      val original = fixture(codes, width, hit, inline)
      val result = reduce(original)
      assert(depth(result, mux = true) == 0)
      assert(depth(result) == 4)
      // Reusing comparisons preserves swapped operands, narrow constants and
      // constants wider than the selector, including unreachable case values.
      assert(body(result).collect { case n: DefNode if n.name.startsWith("cmp_") => n } ==
        body(original).collect { case n: DefNode if n.name.startsWith("cmp_") => n })
      firrtl.passes.CheckTypes.run(result)
      firrtl.passes.CheckWidths.run(result)
      for (addr <- 0 until (1 << width)) {
        val actual = evaluate(result, addr)
        assert(actual("out") == (if (codes.contains(addr)) hit else 1 - hit))
        assert(actual("out") == evaluate(original, addr)("out"))
        assert(actual("probe") == evaluate(original, addr)("probe"))
      }
      assert(ReduceConstantMuxChains.run(result) == result)
    }
  }

  it should "reduce 193 mux dependencies to eight OR levels and retain the default" in {
    val original = fixture(0 until 193, width = 12)
    val (state, stats) = ReduceConstantMuxChains.executeWithStats(CircuitState(original, Seq.empty))
    assert(stats == ReduceConstantMuxChains.Stats(1, 193, 193))
    val result = BalanceAssociativeOps.run(state.circuit)
    assert(depth(original, mux = true) == 193)
    assert(depth(result, mux = true) == 0 && depth(result) == 8)
    for (addr <- 0 until 4096)
      assert(evaluate(result, addr)("out") == (if (addr < 193) 0 else 1))
    firrtl.passes.CheckTypes.run(result)
    firrtl.passes.CheckWidths.run(result)
    val graph = StatementGraph(result)
    val external = Extract.findExternalPorts(result)
    assert(graph.nodeRange().filter(id => graph.idToStmt(id) == EmptyStmt)
      .map(graph.idToName).forall(external.contains))
    new Renamer().populateFromSG(graph, external)
  }

  it should "respect the minimum chain length" in {
    for (length <- 1 until ReduceConstantMuxChains.minChainLength) {
      val c = fixture(0 until length)
      assert(ReduceConstantMuxChains.run(c) == c)
    }
    assert(depth(reduce(fixture(0 until ReduceConstantMuxChains.minChainLength))) == 3)
  }

  it should "leave nonmatching maximal chains unchanged" in {
    val original = fixture(0 until 12)
    val variants = Seq[(String, Expression => Expression)](
      "chain_11" -> { case m: Mux => m.copy(tval = UIntLiteral(1, IntWidth(1))) },
      "chain_0" -> { case m: Mux => m.copy(fval = WRef("probe", bit)) },
      "chain_5" -> { case m: Mux => m.copy(tval = UIntLiteral(0, IntWidth(2))) },
      "cmp_5" -> { case p: DoPrim => p.copy(op = Neq) },
      "cmp_5" -> { case p: DoPrim => p.copy(args = Seq(WRef("other", UIntType(IntWidth(4))), p.args(0))) })
    variants.foreach { case (name, f) =>
      val c = withBody(original, body(original).map {
        case n: DefNode if n.name == name => n.copy(value = f(n.value))
        case s => s
      })
      assert(ReduceConstantMuxChains.run(c) == c, name)
    }
  }

  it should "retain shared and protected intermediate muxes" in {
    val original = fixture(0 until 12)
    val shared = withBody(original, body(original) :+
      Connect(NoInfo, WRef("probe", bit), WRef("chain_5", bit)))
    assert(ReduceConstantMuxChains.run(shared) == shared)
    val annotation = firrtl.transforms.DontTouchAnnotation(
      firrtl.annotations.CircuitTarget(original.main).module(original.main).ref("chain_5"))
    val state = CircuitState(original, Seq(annotation))
    assert(ReduceConstantMuxChains.execute(state) == state)
  }

  it should "follow local aliases without changing external modules or annotations" in {
    val original = fixture(0 until 12)
    val nodes = body(original).flatMap {
      case n @ DefNode(_, "chain_5", m: Mux) => Seq(
        DefNode(NoInfo, "tail_alias", m.fval),
        n.copy(value = m.copy(fval = WRef("tail_alias", bit, NodeKind, SourceFlow))))
      case s => Seq(s)
    }
    val ext = ExtModule(NoInfo, "External", Seq.empty, "External", Seq.empty)
    val c = withBody(original, nodes).copy(modules = withBody(original, nodes).modules :+ ext)
    val result = reduce(c)
    assert(result.modules.last == ext && depth(result, mux = true) == 0)
    for (addr <- 0 until 16) assert(evaluate(result, addr)("out") == evaluate(c, addr)("out"))
  }

  it should "allow disabling the rewrite for a reproducible baseline" in {
    val original = fixture(0 until 12)
    val old = sys.props.get("rteaal.reduceConstantMuxChains")
    try {
      sys.props("rteaal.reduceConstantMuxChains") = "false"
      assert(ReduceConstantMuxChains.run(original) == original)
    } finally old match {
      case Some(value) => sys.props("rteaal.reduceConstantMuxChains") = value
      case None => sys.props.remove("rteaal.reduceConstantMuxChains")
    }
  }
}
