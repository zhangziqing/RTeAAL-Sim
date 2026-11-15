package essent

import essent.passes.{BalanceAssociativeOps, BalancePriorityMuxChains}
import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import firrtl.transforms.DontTouchAnnotation
import org.scalatest.flatspec.AnyFlatSpec

import scala.collection.mutable

class BalancePriorityMuxChainsTest extends AnyFlatSpec {
  private val bit = UIntType(IntWidth(1))
  private def uint(w: Int): UIntType = UIntType(IntWidth(w))
  private def ref(name: String, t: Type): Expression = WRef(name, t, NodeKind, SourceFlow)
  private def lit(value: BigInt, w: Int): Expression = UIntLiteral(value, IntWidth(w))
  private def body(c: Circuit): Seq[Statement] = c.modules.head.asInstanceOf[Module].body match {
    case b: Block => b.stmts
    case s => Seq(s)
  }
  private def withBody(c: Circuit, statements: Seq[Statement]): Circuit =
    c.copy(modules = c.modules.updated(0,
      c.modules.head.asInstanceOf[Module].copy(body = Block(statements))))

  // Pairs are in priority order, independent of node declaration order.
  private def chain(pairs: Seq[(Expression, Expression)], default: Expression,
      ports: Seq[Port], inline: Boolean = false, alias: Boolean = false): Circuit = {
    val statements = mutable.ArrayBuffer.empty[Statement]
    var tail = default
    pairs.indices.reverse.foreach { i =>
      if (alias && i == 3) {
        statements += DefNode(NoInfo, "tail_alias", tail)
        tail = ref("tail_alias", default.tpe)
      }
      val value = Mux(pairs(i)._1, pairs(i)._2, tail, default.tpe)
      if (!inline) statements += DefNode(NoInfo, s"chain_$i", value)
      tail = if (inline) value else ref(s"chain_$i", default.tpe)
    }
    statements += Connect(NoInfo, WRef("out", default.tpe, PortKind, SinkFlow), tail)
    Circuit(NoInfo, Seq(Module(NoInfo, "PriorityProbe",
      ports :+ Port(NoInfo, "out", Output, default.tpe), Block(statements.toVector))), "PriorityProbe")
  }
  private def fixture(n: Int, w: Int = 8, inline: Boolean = false,
      alias: Boolean = false): Circuit = {
    val ports = (0 until n).flatMap(i => Seq(Port(NoInfo, s"c$i", Input, bit),
      Port(NoInfo, s"v$i", Input, uint(w)))) :+ Port(NoInfo, "default", Input, uint(w))
    chain((0 until n).map(i => ref(s"c$i", bit) -> ref(s"v$i", uint(w))),
      ref("default", uint(w)), ports, inline, alias)
  }
  private def twoArmFixture(n: Int, w: Int = 8): Circuit = {
    val ports = (0 until n).flatMap(i => Seq(
      Port(NoInfo, s"a$i", Input, bit), Port(NoInfo, s"av$i", Input, uint(w)),
      Port(NoInfo, s"b$i", Input, bit), Port(NoInfo, s"bv$i", Input, uint(w)))) ++
      Seq(Port(NoInfo, "fire", Input, bit), Port(NoInfo, "out", Output, uint(w)))
    val statements = mutable.ArrayBuffer.empty[Statement]
    def build(prefix: String): Expression = {
      var tail: Expression = ref(s"${prefix}v0", uint(w))
      (0 until n).reverse.foreach { i =>
        val value = Mux(ref(s"$prefix$i", bit), ref(s"${prefix}v$i", uint(w)), tail, uint(w))
        statements += DefNode(NoInfo, s"${prefix}chain_$i", value)
        tail = ref(s"${prefix}chain_$i", uint(w))
      }
      tail
    }
    val a = build("a")
    val b = build("b")
    statements += Connect(NoInfo, WRef("out", uint(w), PortKind, SinkFlow),
      Mux(ref("fire", bit), a, b, uint(w)))
    Circuit(NoInfo, Seq(Module(NoInfo, "TwoArmProbe", ports, Block(statements.toVector))),
      "TwoArmProbe")
  }
  private def evaluate(c: Circuit, inputs: Map[String, BigInt]): BigInt = {
    val definitions = body(c).collect { case n: DefNode => n.name -> n.value }.toMap
    val values = mutable.HashMap.from(inputs)
    def eval(e: Expression): BigInt = e match {
      case r: Reference => values.getOrElseUpdate(r.name, eval(definitions(r.name)))
      case l: UIntLiteral => l.value
      case Mux(cond, t, f, _) => eval(if (eval(cond) != 0) t else f)
      case DoPrim(Or, args, _, _) => eval(args(0)) | eval(args(1))
      case DoPrim(And, args, _, _) => eval(args(0)) & eval(args(1))
      case DoPrim(Eq, args, _, _) => if (eval(args(0)) == eval(args(1))) BigInt(1) else BigInt(0)
      case DoPrim(Bits, args, consts, _) =>
        (eval(args.head) >> consts(1).toInt) & ((BigInt(1) << (consts.head - consts(1) + 1).toInt) - 1)
      case x => fail(s"Unexpected test expression: $x")
    }
    body(c).collectFirst { case Connect(_, r: Reference, e) if r.name == "out" => eval(e) }.get
  }
  private def firstHit(hits: Seq[Boolean], candidates: Seq[BigInt], default: BigInt): BigInt =
    hits.indices.find(hits).map(candidates).getOrElse(default)

  private def depth(c: Circuit): Int = {
    val definitions = body(c).collect { case n: DefNode => n.name -> n.value }.toMap
    val cached = mutable.HashMap.empty[String, Int]
    def d(e: Expression): Int = e match {
      case r: Reference => cached.getOrElseUpdate(r.name, definitions.get(r.name).map(d).getOrElse(0))
      case _: Literal => 0
      case _ =>
        var maximum = 0
        e.mapExpr { child => maximum = maximum.max(d(child)); child }
        maximum + 1
    }
    body(c).collectFirst { case Connect(_, r: Reference, e) if r.name == "out" => d(e) }.get
  }
  private def verifyTypes(c: Circuit): Unit = {
    firrtl.passes.CheckTypes.run(c)
    firrtl.passes.CheckWidths.run(c)
  }

  "BalancePriorityMuxChains" should "preserve first-hit order for all masks and UInt boundaries" in {
    for (n <- Seq(8, 9); w <- Seq(1, 7, 63, 64, 65, 127, 128, 129);
         inline <- Seq(false, true)) {
      val original = fixture(n, w, inline, alias = !inline)
      val (state, stats) = BalancePriorityMuxChains.executeWithStats(CircuitState(original, Seq.empty))
      val result = state.circuit
      assert(stats.chains == 1 && stats.muxes == n && stats.longestChain == n)
      assert(depth(result) <= 32 - Integer.numberOfLeadingZeros(n))
      verifyTypes(result)
      val mask = (BigInt(1) << w) - 1
      val candidates = (0 until n).map(i => (mask - i) & mask)
      for (hitMask <- 0 until (1 << n)) {
        val hits = (0 until n).map(i => (hitMask & (1 << i)) != 0)
        val default = (BigInt(hitMask) | (BigInt(1) << (w - 1))) & mask
        val inputs = (0 until n).flatMap(i => Seq(s"c$i" -> BigInt(if (hits(i)) 1 else 0),
          s"v$i" -> candidates(i))).toMap + ("default" -> default)
        assert(evaluate(result, inputs) == firstHit(hits, candidates, default), s"n=$n w=$w mask=$hitMask")
      }
      assert(BalancePriorityMuxChains.run(result) == result)
    }
  }

  it should "share segment hit nodes and remain stable on long chains" in {
    for (n <- Seq(16, 106, 129, 132)) {
      val original = fixture(n)
      val result = BalancePriorityMuxChains.run(original)
      val ors = body(result).collect { case n @ DefNode(_, _, DoPrim(Or, _, _, _)) => n }
      val uses = mutable.HashMap.empty[String, Int].withDefaultValue(0)
      def count(e: Expression): Expression = {
        e match { case r: Reference => uses(r.name) += 1; case _ => }
        e.mapExpr(count); e
      }
      body(result).foreach(_.mapExpr(count))
      assert(ors.nonEmpty && ors.size < n)
      assert(ors.exists(n => uses(n.name) > 1))
      assert(depth(result) <= 32 - Integer.numberOfLeadingZeros(n))
      assert(BalancePriorityMuxChains.run(result) == result)
      val prepared = BalanceAssociativeOps.run(result)
      assert(BalancePriorityMuxChains.run(prepared) == prepared)
      verifyTypes(result)
    }
  }

  it should "balance both arms of a two-chain selector independently" in {
    val n = 8
    val original = twoArmFixture(n)
    val (state, stats) = BalancePriorityMuxChains.executeWithStats(CircuitState(original, Seq.empty))
    val result = state.circuit
    assert(stats.chains == 2 && stats.muxes == 2 * n && stats.longestChain == n)
    assert(depth(result) < depth(original))
    assert(BalancePriorityMuxChains.run(result) == result)
    verifyTypes(result)
    val aValues = (0 until n).map(i => BigInt(100 + i))
    val bValues = (0 until n).map(i => BigInt(200 + i))
    for (fire <- 0 to 1; aMask <- 0 until (1 << n); bMask <- Seq(0, (1 << n) - 1)) {
      val hitsA = (0 until n).map(i => (aMask & (1 << i)) != 0)
      val hitsB = (0 until n).map(i => (bMask & (1 << i)) != 0)
      val inputs = (0 until n).flatMap(i => Seq(
        s"a$i" -> BigInt(if (hitsA(i)) 1 else 0), s"av$i" -> aValues(i),
        s"b$i" -> BigInt(if (hitsB(i)) 1 else 0), s"bv$i" -> bValues(i))).toMap +
        ("fire" -> BigInt(fire))
      val expected = if (fire != 0) firstHit(hitsA, aValues, aValues(0))
                     else firstHit(hitsB, bValues, bValues(0))
      assert(evaluate(result, inputs) == expected, s"fire=$fire a=$aMask b=$bMask")
    }
  }

  it should "respect thresholds, shared nodes, protected aliases and conditional scopes" in {
    for (n <- 1 until BalancePriorityMuxChains.minChainLength) {
      val c = fixture(n)
      assert(BalancePriorityMuxChains.run(c) == c)
    }
    val original = fixture(16, w = 1, alias = true)
    for (name <- Seq("chain_5", "tail_alias")) {
      val shared = withBody(original, body(original) :+
        DefNode(NoInfo, "observer", ref(name, bit)))
      assert(BalancePriorityMuxChains.run(shared) == shared)
      val conditionUse = withBody(original, body(original).map {
        case n @ DefNode(_, "chain_0", m: Mux) => n.copy(value = m.copy(cond = ref(name, bit)))
        case s => s
      })
      assert(BalancePriorityMuxChains.run(conditionUse) == conditionUse)
      val annotation = DontTouchAnnotation(firrtl.annotations.CircuitTarget(original.main)
        .module(original.main).ref(name))
      val state = CircuitState(original, Seq(annotation))
      assert(BalancePriorityMuxChains.execute(state) == state)
    }
    val conditional = withBody(original, Seq(Conditionally(NoInfo, ref("c0", bit),
      Block(body(original)), EmptyStmt)))
    assert(BalancePriorityMuxChains.run(conditional) == conditional)
  }

  it should "leave unsupported maximal chains intact" in {
    val original = fixture(16)
    val variants: Seq[(String, Mux => Mux)] = Seq(
      "wide condition" -> (_.copy(cond = ref("v0", uint(8)))),
      "mixed data width" -> (_.copy(tval = lit(1, 7))),
      "unknown result width" -> (_.copy(tpe = UIntType(UnknownWidth))),
      "signed result" -> (_.copy(tpe = SIntType(IntWidth(8)))),
      "unknown default width" -> (_.copy(fval = ref("default", UIntType(UnknownWidth)))))
    variants.foreach { case (label, transform) =>
      val bad = withBody(original, body(original).map {
        case n @ DefNode(_, "chain_8", m: Mux) => n.copy(value = transform(m))
        case s => s
      })
      assert(BalancePriorityMuxChains.run(bad) == bad, label)
    }
    val aliased = fixture(16, alias = true)
    val mismatchedAlias = withBody(aliased, body(aliased).map {
      case n @ DefNode(_, "tail_alias", _) => n.copy(value = ref("chain_4", uint(7)))
      case s => s
    })
    assert(BalancePriorityMuxChains.run(mismatchedAlias) == mismatchedAlias)
  }

  it should "retain dense lookup chains including a dense suffix below priority overrides" in {
    val selector = ref("index", uint(7))
    val ports = Seq(Port(NoInfo, "index", Input, uint(7)), Port(NoInfo, "override", Input, bit))
    val dense = (127 to 1 by -1).map(i =>
      DoPrim(Eq, Seq(lit(i, 7), selector), Seq.empty, bit) -> lit(i, 8))
    for (pairs <- Seq(dense, (ref("override", bit) -> lit(213, 8)) +: dense)) {
      val original = chain(pairs, lit(37, 8), ports)
      val (state, stats) = BalancePriorityMuxChains.executeWithStats(CircuitState(original, Seq.empty))
      assert(state.circuit == original && stats.chains == 0 && stats.lookupChainsSkipped >= 1)
    }
  }

  it should "preserve CLZ_8 high-bit priority and its zero-input result 106" in {
    val input = ref("input", uint(107))
    val pairs = (106 to 1 by -1).map(i =>
      DoPrim(Bits, Seq(input), Seq(BigInt(i), BigInt(i)), bit) -> lit(106 - i, 7))
    val original = chain(pairs, lit(106, 7), Seq(Port(NoInfo, "input", Input, uint(107))))
    val result = BalanceAssociativeOps.run(BalancePriorityMuxChains.run(original))
    assert(depth(original) == 107 && depth(result) <= 8)
    val samples = Seq(BigInt(0), (BigInt(1) << 107) - 1) ++
      (0 until 107).map(BigInt(1) << _) ++
      (for (i <- 0 until 107; j <- 0 until i) yield (BigInt(1) << i) | (BigInt(1) << j))
    samples.foreach { value =>
      val expected = if (value == 0) BigInt(106) else BigInt(107 - value.bitLength)
      assert(evaluate(result, Map("input" -> value)) == expected, value.toString(16))
    }
    verifyTypes(result)
  }

  it should "preserve all LFST indices and all lane-five bypass combinations" in {
    // StoreSet.scala assigns j=0..4 in order; j=4 has highest bypass priority.
    // The prepared LFST chain selects row31/col3 down to row0/col1, default row0/col0.
    val ports = Seq(Port(NoInfo, "ssid", Input, uint(5)), Port(NoInfo, "ptr", Input, uint(2))) ++
      (0 until 128).map(i => Port(NoInfo, s"table$i", Input, uint(8))) ++
      (0 until 5).flatMap(i => Seq(Port(NoInfo, s"hit$i", Input, bit),
        Port(NoInfo, s"bypass$i", Input, uint(8))))
    val table = (127 to 1 by -1).map { i =>
      val row = DoPrim(Eq, Seq(lit(i / 4, 5), ref("ssid", uint(5))), Seq.empty, bit)
      val col = DoPrim(Eq, Seq(lit(i % 4, 2), ref("ptr", uint(2))), Seq.empty, bit)
      DoPrim(And, Seq(row, col), Seq.empty, bit) -> ref(s"table$i", uint(8))
    }
    val bypass = (4 to 0 by -1).map(i => ref(s"hit$i", bit) -> ref(s"bypass$i", uint(8)))
    val original = chain(bypass ++ table, ref("table0", uint(8)), ports, inline = true)
    val result = BalanceAssociativeOps.run(BalancePriorityMuxChains.run(original))
    assert(depth(result) < depth(original) && depth(result) <= 10)
    for (phase <- 0 to 1; index <- 0 until 128; mask <- 0 until 32) {
      val candidates = (0 until 128).map(i => BigInt((i * 37 + phase * 91) & 255))
      val bypassValues = (0 until 5).map(i => BigInt(250 - i * 17 - phase))
      val hits = (4 to 0 by -1).map(i => (mask & (1 << i)) != 0)
      val inputs = (0 until 128).map(i => s"table$i" -> candidates(i)).toMap ++
        (0 until 5).flatMap(i => Seq(s"hit$i" -> BigInt((mask >> i) & 1),
          s"bypass$i" -> bypassValues(i))) ++
        Map("ssid" -> BigInt(index / 4), "ptr" -> BigInt(index % 4))
      val expected = firstHit(hits, bypassValues.reverse, candidates(index))
      assert(evaluate(result, inputs) == expected, s"index=$index mask=$mask phase=$phase")
    }
    verifyTypes(result)
  }

  it should "preserve annotations and external modules and integrate with the statement graph" in {
    val original = fixture(16)
    val ext = ExtModule(NoInfo, "External", Seq.empty, "External", Seq.empty)
    val c = original.copy(modules = original.modules :+ ext)
    val annotation = DontTouchAnnotation(firrtl.annotations.CircuitTarget(c.main).module(c.main).ref("v0"))
    val state = CircuitState(c, Seq(annotation))
    val result = BalancePriorityMuxChains.execute(state)
    assert(result.annotations == state.annotations && result.circuit.modules.last == ext)
    val graph = StatementGraph(result.circuit)
    val external = Extract.findExternalPorts(result.circuit)
    assert(graph.nodeRange().filter(id => graph.idToStmt(id) == EmptyStmt)
      .map(graph.idToName).forall(external.contains))
    new Renamer().populateFromSG(graph, external)
  }

  it should "support a separately disabled baseline" in {
    val original = fixture(16)
    val old = sys.props.get("rteaal.balancePriorityMuxChains")
    try {
      sys.props("rteaal.balancePriorityMuxChains") = "false"
      assert(BalancePriorityMuxChains.run(original) == original)
    } finally old match {
      case Some(value) => sys.props("rteaal.balancePriorityMuxChains") = value
      case None => sys.props.remove("rteaal.balancePriorityMuxChains")
    }
  }
}
