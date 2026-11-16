package essent

import org.scalatest.flatspec.AnyFlatSpec
import scala.collection.mutable.{HashMap, HashSet}

class BalanceAndOrOpsTest extends AnyFlatSpec {
  private class Graph {
    val ops = HashMap.empty[String, HashMap[String, HashSet[Int]]]
    val users, producers = HashMap.empty[String, HashSet[String]]
    val outputs = HashMap.empty[String, String]
    val widths = HashMap.empty[String, Int]
    def add(kind: String, out: String, width: Int, inputs: String*): String = {
      val op = s"${kind}_+_${ops.size}"
      val args = HashMap.empty[String, HashSet[Int]]
      inputs.zipWithIndex.foreach { case (in, i) =>
        args.getOrElseUpdate(in, HashSet.empty) += i
        users.getOrElseUpdate(in, HashSet.empty) += op
      }
      ops(op) = args; outputs(op) = out; producers(out) = HashSet(op)
      widths(op) = width; widths(out) = width
      op
    }
    def and(a: String, b: String, out: String): String = add("and", out, widths(a), a, b)
    def or(a: String, b: String, out: String): String = add("or", out, widths(a), a, b)
    def arguments(op: String): Map[Int, String] =
      ops(op).toSeq.flatMap { case (signal, ports) => ports.map(_ -> signal) }.toMap
    def evaluate(out: String, values: Map[String, BigInt]): BigInt = values.getOrElse(out, {
      val op = producers(out).head
      val args = arguments(op)
      if (op.startsWith("and")) evaluate(args(0), values) & evaluate(args(1), values)
      else evaluate(args(0), values) | evaluate(args(1), values)
    })
    def depth(out: String): Int = producers.get(out).fold(0) { ps =>
      1 + ps.iterator.flatMap(op => ops(op).keys).map(depth).max
    }
    def balance(protectedNames: Set[String] = Set.empty): BalanceAndOrOps.Stats =
      BalanceAndOrOps.run(ops, users, producers, outputs, widths, protectedNames)
    def check(): Unit = {
      ops.foreach { case (op, args) =>
        assert(producers.get(outputs(op)) == Some(HashSet(op)), op)
        args.keys.foreach(signal => assert(users(signal)(op), s"$op $signal"))
      }
      users.foreach { case (signal, us) => us.foreach(op => assert(ops(op).contains(signal))) }
      producers.foreach { case (signal, ps) =>
        assert(ps.size == 1, signal)
        assert(ops.contains(ps.head), signal)
      }
    }
  }

  private def chain(kind: String, count: Int): (Graph, String) = {
    val g = new Graph
    (0 until count).foreach(i => g.widths(s"x$i") = 64)
    var out = "x0"
    (1 until count).foreach { i =>
      val next = s"n$i"
      if (kind == "and") g.and(out, s"x$i", next) else g.or(out, s"x$i", next)
      out = next
    }
    (g, out)
  }

  behavior of "BalanceAndOrOps"
  it should "balance single-use AND and OR chains to logarithmic depth" in {
    for (kind <- Seq("and", "or"); count <- Seq(4, 5, 17, 128)) {
      val (g, out) = chain(kind, count)
      val before = g.ops.size
      val original = g.outputs.toMap
      val stats = g.balance()
      assert(stats.groups == 1, s"$kind $count $stats")
      assert(stats.clones == 0)
      assert(g.depth(out) == 32 - Integer.numberOfLeadingZeros(count - 1))
      assert(g.ops.size == before)
      assert(g.outputs.toMap == original)
      g.check()
      val random = new scala.util.Random(17)
      for (round <- 0 until 64) {
        val values = (0 until count).map(i => s"x$i" -> BigInt(64, random)).toMap
        val expected = if (kind == "and") values.values.reduce(_ & _) else values.values.reduce(_ | _)
        assert(g.evaluate(out, values) == expected)
      }
    }
  }

  it should "duplicate a shared critical cone and keep the original for other users" in {
    val g = new Graph
    (0 until 6).foreach(i => g.widths(s"x$i") = 64)
    val s0 = g.and("x0", "x1", "s0")
    val s1 = g.and("s0", "x2", "s1")
    val s2 = g.and("s1", "x3", "s2")     // shared, depth 3
    val p = g.and("s2", "x4", "p")        // depth 4, critical
    val q = g.and("s2", "x5", "q")        // other user, depth 4
    val beforeDepth = g.depth("p")
    val beforeOps = g.ops.size
    val stats = g.balance()
    assert(stats.groups >= 1 && stats.clones > 0, stats.toString)
    assert(g.depth("p") < beforeDepth, s"p depth ${g.depth("p")} vs $beforeDepth")
    assert(g.ops.size > beforeOps)
    assert(g.producers("s2").size == 1 && g.producers("s2").head == s2)
    assert(g.ops.contains(p) && g.ops.contains(q))
    g.check()
    val random = new scala.util.Random(23)
    for (round <- 0 until 128) {
      val values = (0 until 6).map(i => s"x$i" -> BigInt(64, random)).toMap
      val expectedP = ((((values("x0") & values("x1")) & values("x2")) & values("x3")) & values("x4"))
      val expectedQ = ((((values("x0") & values("x1")) & values("x2")) & values("x3")) & values("x5"))
      assert(g.evaluate("p", values) == expectedP)
      assert(g.evaluate("q", values) == expectedQ)
    }
  }

  it should "not duplicate when duplication is disabled or the shared node is protected" in {
    def build(): (Graph, String, String, String) = {
      val g = new Graph
      (0 until 6).foreach(i => g.widths(s"x$i") = 64)
      val s0 = g.and("x0", "x1", "s0")
      val s1 = g.and("s0", "x2", "s1")
      val s2 = g.and("s1", "x3", "s2")
      val p = g.and("s2", "x4", "p")
      val q = g.and("s2", "x5", "q")
      (g, s2, p, q)
    }
    val previous = sys.props.get("rteaal.balanceAndOrDuplication")
    try {
      sys.props("rteaal.balanceAndOrDuplication") = "false"
      val (g, _, p, _) = build()
      val before = g.depth("p")
      val stats = g.balance()
      assert(stats.clones == 0)
      assert(g.depth("p") == before)
      g.check()
    } finally {
      previous match {
        case Some(value) => sys.props("rteaal.balanceAndOrDuplication") = value
        case None => sys.props.remove("rteaal.balanceAndOrDuplication")
      }
    }
    val (g, s2, _, _) = build()
    val before = g.depth("p")
    val stats = g.balance(Set("s2"))
    assert(stats.clones == 0)
    assert(g.depth("p") == before)
    g.check()
  }
}
