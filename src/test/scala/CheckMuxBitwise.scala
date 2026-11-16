import essent.passes.{BalanceAssociativeOps, FactorMuxBitwise}
import firrtl._
import firrtl.ir._
import firrtl.PrimOps._
import scala.collection.mutable

/** One small semantic and depth smoke test for the shared bitwise mux rule. */
object CheckMuxBitwise {
  def main(args: Array[String]): Unit = {
    val bit = UIntType(IntWidth(1))
    var comparisons = 0
    for (op <- Seq(And, Or, Xor); width <- Seq(1, 8, 65)) {
      val tpe = UIntType(IntWidth(width))
      def ref(n: String, t: Type = tpe): Expression = WRef(n, t, NodeKind, SourceFlow)
      val nodes = mutable.ArrayBuffer.empty[Statement]
      var old = ref("old")
      for (i <- 0 until 8) {
        val operands = if (i % 2 == 0) Seq(old, ref("x")) else Seq(ref("x"), old)
        nodes += DefNode(NoInfo, s"branch$i", DoPrim(op, operands, Seq.empty, tpe))
        val branch = ref(s"branch$i")
        nodes += DefNode(NoInfo, s"step$i", Mux(ref("sel", bit),
          if (i % 2 == 0) branch else old, if (i % 2 == 0) old else branch, tpe))
        old = ref(s"step$i")
      }
      nodes += DefNode(NoInfo, "left", DoPrim(op, Seq(old, ref("a")), Seq.empty, tpe))
      nodes += DefNode(NoInfo, "right", DoPrim(op, Seq(ref("b"), old), Seq.empty, tpe))
      nodes += DefNode(NoInfo, "result", Mux(ref("sel", bit), ref("left"), ref("right"), tpe))
      nodes += Connect(NoInfo, WRef("out", tpe, PortKind, SinkFlow), ref("result"))
      val ports = Seq("old", "x", "a", "b").map(n => Port(NoInfo, n, Input, tpe)) ++
        Seq(Port(NoInfo, "sel", Input, bit), Port(NoInfo, "out", Output, tpe))
      val original = Circuit(NoInfo, Seq(Module(NoInfo, "Probe", ports, Block(nodes.toVector))), "Probe")
      val (factored, stats) = FactorMuxBitwise.executeWithStats(CircuitState(original, Seq.empty))
      require(stats.andMuxes + stats.orMuxes + stats.xorMuxes == 9, stats.toString)
      val result = BalanceAssociativeOps.execute(factored).circuit
      firrtl.passes.CheckTypes.run(result)
      firrtl.passes.CheckWidths.run(result)
      def definitions(c: Circuit): Map[String, Expression] =
        c.modules.head.asInstanceOf[Module].body.asInstanceOf[Block].stmts
          .collect { case n: DefNode => n.name -> n.value }.toMap
      def evaluate(c: Circuit, inputs: Map[String, BigInt]): BigInt = {
        val defs = definitions(c)
        val values = mutable.HashMap.from(inputs)
        def eval(e: Expression): BigInt = e match {
          case r: Reference => values.getOrElseUpdate(r.name, eval(defs(r.name)))
          case l: UIntLiteral => l.value
          case Mux(s, t, f, _) => eval(if (eval(s) != 0) t else f)
          case DoPrim(And, a, _, _) => eval(a(0)) & eval(a(1))
          case DoPrim(Or, a, _, _) => eval(a(0)) | eval(a(1))
          case DoPrim(Xor, a, _, _) => eval(a(0)) ^ eval(a(1))
          case other => sys.error(s"Unexpected smoke expression: $other")
        }
        eval(ref("result"))
      }
      def depth(c: Circuit): Int = {
        val defs = definitions(c)
        val cached = mutable.HashMap.empty[String, Int]
        def d(e: Expression): Int = e match {
          case r: Reference => cached.getOrElseUpdate(r.name, defs.get(r.name).map(d).getOrElse(0))
          case _: Literal => 0
          case _ =>
            var maximum = 0
            e.mapExpr { x => maximum = maximum.max(d(x)); x }
            maximum + 1
        }
        d(ref("result"))
      }
      val mask = (BigInt(1) << width) - 1
      for (sel <- 0 to 1; value <- Seq(BigInt(0), mask, BigInt(1) << (width - 1))) {
        val inputs = Map("sel" -> BigInt(sel), "old" -> value, "x" -> (mask ^ value),
          "a" -> BigInt(1), "b" -> mask)
        require(evaluate(original, inputs) == evaluate(result, inputs), s"$op width=$width sel=$sel")
        comparisons += 1
      }
      require(depth(result) < depth(original), s"$op did not expose the reduction")
      println(s"$op width=$width depth=${depth(original)}->${depth(result)} removed=${stats.removedNodes}")
    }
    println(s"PASS one bitwise mux smoke: $comparisons comparisons; no ScalaTest suites")
  }
}
