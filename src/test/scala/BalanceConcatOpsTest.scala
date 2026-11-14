package essent

import org.scalatest.flatspec.AnyFlatSpec
import scala.collection.mutable.{HashMap, HashSet}

class BalanceConcatOpsTest extends AnyFlatSpec {
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
    def cat(a: String, b: String, out: String): String =
      add("cat", out, widths(a) + widths(b), a, b, widths(b).toString)
    def arguments(op: String): Map[Int, String] =
      ops(op).toSeq.flatMap { case (s, ps) => ps.map(_ -> s) }.toMap
    def evaluate(out: String, values: Map[String, BigInt]): BigInt = values.getOrElse(out, {
      if (out.forall(_.isDigit)) BigInt(out)
      else {
        val op = producers(out).head; val a = arguments(op)
        if (op.startsWith("assign")) evaluate(a(0), values)
        else (evaluate(a(0), values) << a(2).toInt) | evaluate(a(1), values)
      }
    })
    def depth(out: String): Int = producers.get(out).fold(0) { ps =>
      1 + ps.iterator.flatMap(op => ops(op).keys).map(depth).max
    }
    def balance(protectedNames: Set[String] = Set.empty): BalanceConcatOps.Stats =
      BalanceConcatOps.run(ops, users, producers, outputs, widths, protectedNames)
    def check(): Unit = {
      ops.foreach { case (op, args) =>
        assert(producers(outputs(op)) == HashSet(op))
        args.keys.foreach(s => assert(users(s)(op)))
        if (op.startsWith("cat")) {
          val a = arguments(op)
          assert(a.keySet == Set(0, 1, 2))
          assert(widths(outputs(op)) == widths(a(0)) + widths(a(1)))
          assert(a(2).toInt == widths(a(1)))
        }
      }
      users.foreach { case (s, us) => us.foreach(op => assert(ops(op).contains(s))) }
    }
  }
  private def chain(ws: Seq[Int], right: Boolean = false): (Graph, String) = {
    val g = new Graph
    ws.zipWithIndex.foreach { case (w, i) => g.widths(s"x$i") = w }
    var out = if (right) s"x${ws.size - 1}" else "x0"
    val indices = if (right) ws.indices.dropRight(1).reverse else ws.indices.drop(1)
    indices.foreach { i =>
      val next = s"n$i"
      if (right) g.cat(s"x$i", out, next) else g.cat(out, s"x$i", next)
      out = next
    }
    (g, out)
  }

  behavior of "BalanceConcatOps"
  it should "keep ordered fields and widths while reducing left and right chains" in {
    val random = new scala.util.Random(311)
    for (ws <- Seq(Seq.fill(7)(1), Seq.fill(8)(8), Seq(1, 7, 8, 16, 31, 1), Seq.fill(64)(1));
         right <- Seq(false, true)) {
      val (g, out) = chain(ws, right)
      val before = g.ops.size; val publicOutputs = g.outputs.toMap
      assert(g.balance().groups == 1)
      assert(g.depth(out) == 32 - Integer.numberOfLeadingZeros(ws.size - 1))
      assert(g.ops.size == before && g.outputs.toMap == publicOutputs)
      for (round <- 0 until 128) {
        val values = ws.zipWithIndex.map { case (w, i) =>
          s"x$i" -> (if (round == 0) BigInt(0) else if (round == 1) (BigInt(1) << w) - 1
                     else BigInt(w, random))
        }.toMap
        val bits = ws.zipWithIndex.map { case (w, i) =>
          val b = values(s"x$i").toString(2); "0" * (w - b.length) + b
        }.mkString
        assert(g.evaluate(out, values) == BigInt(bits, 2))
      }
      g.check(); assert(g.balance() == BalanceConcatOps.Stats())
    }
  }
  it should "retain shared, protected, aliased and lookup-referenced intermediates" in {
    for (mode <- 0 until 5) {
      val (g, out) = chain(Seq.fill(8)(4))
      val producer = g.producers("n3").head
      val protectedNames = mode match {
        case 0 => Set("n3")
        case 1 => Set(producer)
        case 2 =>
          g.add("assign", "observed", 16, "n3"); Set.empty[String]
        case 3 =>
          g.producers("alias") = HashSet(producer); g.widths("alias") = 16; Set.empty[String]
        case _ =>
          val op = g.add("assign", "observed", 16, "n3")
          g.users("n3") -= op; Set.empty[String]
      }
      val values = (0 until 8).map(i => s"x$i" -> BigInt(i)).toMap
      val expected = g.evaluate(out, values)
      val intermediate = g.evaluate("n3", values)
      g.balance(protectedNames)
      assert(g.evaluate(out, values) == expected && g.evaluate("n3", values) == intermediate)
      assert(g.producers("n3") == HashSet(producer))
      if (mode == 1) assert(g.arguments(producer)(0) == "n2")
    }
  }
  it should "retain repeated intermediate producers without duplicating their computation" in {
    val (g, out) = chain(Seq.fill(4)(4))
    g.cat(out, out, "repeat")
    val count = g.ops.size
    val values = (0 until 4).map(i => s"x$i" -> BigInt(i + 1)).toMap
    val expected = g.evaluate("repeat", values)
    g.balance()
    assert(g.ops.size == count && g.evaluate("repeat", values) == expected)
    g.check()
  }
  it should "skip unknown widths, mismatched shifts, wide results and late-input regressions" in {
    for (mode <- 0 until 4) {
      val (g, out) = chain(Seq.fill(8)(if (mode == 2) 9 else 1))
      mode match {
        case 0 => g.widths.remove("x0")
        case 1 =>
          val op = g.producers("n4").head
          g.ops(op)("2") = g.ops(op).remove("1").get
        case 3 =>
          g.widths("source") = 1
          var previous = "source"
          for (i <- 0 until 20) { g.add("assign", s"delay$i", 1, previous); previous = s"delay$i" }
          val op = g.producers(out).head
          g.users("x7") -= op; g.ops(op)(previous) = g.ops(op).remove("x7").get
          g.users.getOrElseUpdate(previous, HashSet.empty) += op
        case _ =>
      }
      val before = g.depth(out)
      val count = g.ops.size
      g.balance()
      assert(g.depth(out) <= before && g.ops.size == count)
      if (mode == 3) assert(g.depth(out) == before)
    }
  }
}
