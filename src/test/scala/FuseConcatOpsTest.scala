package essent

import org.scalatest.flatspec.AnyFlatSpec
import scala.collection.mutable.{HashMap, HashSet}

class FuseConcatOpsTest extends AnyFlatSpec {
  private class Graph {
    val ops = HashMap.empty[String, HashMap[String, HashSet[Int]]]
    val users, producers = HashMap.empty[String, HashSet[String]]
    val outputs = HashMap.empty[String, String]
    val widths = HashMap.empty[String, Int]
    def cat(left: String, right: String, out: String): String = {
      val name = s"cat_+_${ops.size}"
      val shift = widths(right).toString
      val args = HashMap.empty[String, HashSet[Int]]
      Seq(left, right, shift).zipWithIndex.foreach { case (in, i) =>
        args.getOrElseUpdate(in, HashSet.empty) += i
        users.getOrElseUpdate(in, HashSet.empty) += name
      }
      ops(name) = args
      outputs(name) = out
      producers(out) = HashSet(name)
      widths(out) = widths(left) + widths(right)
      widths(name) = widths(out)
      name
    }
    def fuse(protectedNames: Set[String] = Set.empty): FuseConcatOps.Stats =
      FuseConcatOps.run(ops, users, producers, outputs, widths, protectedNames)
    def result(out: String, values: Map[String, BigInt]): BigInt = {
      val op = producers(out).head
      val args = ops(op).toSeq.flatMap { case (in, ps) => ps.map(_ -> in) }.toMap
      assert(op.startsWith("catn_+_"))
      (0 until args(0).toInt).foldLeft(BigInt(0)) { (acc, i) =>
        acc | (values(args(1 + 2 * i)) << args(2 + 2 * i).toInt)
      }
    }
    def checkEdges(): Unit = {
      ops.foreach { case (op, args) =>
        assert(producers(outputs(op)) == HashSet(op))
        args.keys.foreach(in => assert(users(in)(op)))
      }
      users.foreach { case (in, us) => us.foreach(op => assert(ops(op).contains(in))) }
    }
  }
  private def chain(ws: Seq[Int]): Graph = {
    val g = new Graph
    ws.zipWithIndex.foreach { case (w, i) => g.widths(s"x$i") = w }
    var previous = "x0"
    ws.indices.drop(1).foreach { i =>
      g.cat(previous, s"x$i", s"n$i")
      previous = s"n$i"
    }
    g
  }

  behavior of "FuseConcatOps"

  it should "preserve field order and every bit through the 64-bit boundary" in {
    val random = new scala.util.Random(217)
    Seq(Seq(1, 1, 1), Seq(7, 8, 16), Seq(1, 31, 32), Seq(32, 31, 1),
      Seq.fill(64)(1)).foreach { ws =>
      val g = chain(ws)
      val stats = g.fuse()
      assert(stats.groups == 1 && stats.removed == ws.size - 2 && stats.maxInputs == ws.size)
      assert(g.ops.size == 1)
      for (round <- 0 until 256) {
        val values = ws.zipWithIndex.map { case (w, i) =>
          s"x$i" -> (if (round == 0) BigInt(0) else if (round == 1) (BigInt(1) << w) - 1
                     else BigInt(w, random))
        }.toMap
        // Independent reference joins fixed-width bit strings, not offsets.
        val bits = ws.zipWithIndex.map { case (w, i) =>
          val s = values(s"x$i").toString(2)
          "0" * (w - s.length) + s
        }.mkString
        assert(g.result(s"n${ws.size - 1}", values) == BigInt(bits, 2))
      }
      g.checkEdges()
      assert(g.fuse() == FuseConcatOps.Stats())
    }
  }

  it should "fuse both branches and retain repeated input occurrences" in {
    val g = new Graph
    g.widths("x") = 8
    g.cat("x", "x", "a")
    g.cat("x", "x", "b")
    g.cat("a", "b", "out")
    assert(g.fuse().maxInputs == 4)
    for (x <- 0 until 256) assert(g.result("out", Map("x" -> BigInt(x))) == BigInt(x) * BigInt("01010101", 16))
    g.checkEdges()
  }

  it should "retain shared and observed intermediate producers" in {
    for (protectedNode <- Seq(false, true)) {
      val g = chain(Seq(8, 8, 8))
      if (!protectedNode) {
        g.users("n1") += "assign_+_9"
        g.ops("assign_+_9") = HashMap("n1" -> HashSet(0))
        g.outputs("assign_+_9") = "observed"
        g.producers("observed") = HashSet("assign_+_9")
      }
      assert(g.fuse(if (protectedNode) Set("n1") else Set.empty).groups == 0)
      assert(g.producers("n1").nonEmpty)
      g.checkEdges()
    }
  }

  it should "leave wide, truncated and unknown-width concat operations intact" in {
    val wide = chain(Seq(32, 32, 1))
    assert(wide.fuse().groups == 0)
    val truncated = chain(Seq(8, 8, 8))
    truncated.widths("n1") = 7
    assert(truncated.fuse().groups == 0)
    val unknown = chain(Seq(8, 8, 8))
    unknown.widths.remove("x0")
    assert(unknown.fuse().groups == 0)
  }

  it should "preserve producers with additional output aliases" in {
    val g = chain(Seq(8, 8, 8))
    val producer = g.producers("n1").head
    g.producers("alias") = HashSet(producer)
    g.widths("alias") = 16
    g.cat("alias", "x2", "other")
    assert(g.fuse().groups == 0)
    assert(g.ops.contains(producer))
    assert(g.producers("alias").forall(g.ops.contains))
    g.checkEdges()
  }

  it should "check actual users when reverse edges omit another consumer" in {
    val g = chain(Seq(8, 8, 8))
    val extra = g.cat("n1", "x2", "other")
    g.users("n1") -= extra
    assert(g.fuse().groups == 0)
    assert(g.producers("n1").forall(g.ops.contains))
  }

  it should "preserve operation identities referenced by lookup tables" in {
    val g = chain(Seq(8, 8, 8, 8))
    val lookupTarget = g.producers("n3").head
    assert(g.fuse(Set(lookupTarget)).groups == 1)
    assert(g.ops.contains(lookupTarget))
    assert(g.outputs(lookupTarget) == "n3")
    g.checkEdges()
  }
}
