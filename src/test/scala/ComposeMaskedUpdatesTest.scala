package essent

import essent.SliceGraph._
import essent.ProjectSlices._
import essent.ComposeMaskedUpdates.{Composer, Update}
import org.scalatest.flatspec.AnyFlatSpec

class ComposeMaskedUpdatesTest extends AnyFlatSpec {
  private def chain(n: Int, nested: Boolean = false): ProjectionFixture = {
    val f = new ProjectionFixture
    f.input("state", 1)
    var prior = "state"
    for (i <- 0 until n) {
      f.input(s"e$i", 1); f.input(s"d$i", 1)
      val out = if (i == n - 1) "state@next" else s"stage$i"
      if (nested) {
        f.input(s"p$i", 1)
        f.add("mux", s"path$i", 1, s"p$i", s"d$i", prior)
        f.add("mux", out, 1, s"e$i", s"path$i", prior)
      } else f.add("mux", out, 1, s"e$i", s"d$i", prior)
      prior = out
    }
    f
  }
  private def reference(old: Int, es: Int, ds: Int, n: Int, paths: Int = -1): BigInt =
    (0 until n).foldLeft(BigInt(old)) { (s, i) =>
      if (((es >> i) & (paths >> i) & 1) != 0) BigInt((ds >> i) & 1) else s
    }
  behavior of "ComposeMaskedUpdates"

  it should "exhaustively preserve six ordered updates including no writes and later overwrites" in {
    val f = chain(6)
    val stats = ComposeMaskedUpdates.run(f.graph(states = Set("state")), enabled = true)
    assert(stats.applied == 1)
    for (old <- 0 to 1; es <- 0 until 64; ds <- 0 until 64) {
      val values = (0 until 6).flatMap(i => Seq(s"e$i" -> BigInt((es >> i) & 1),
        s"d$i" -> BigInt((ds >> i) & 1))).toMap + ("state" -> BigInt(old))
      assert(f.evaluate("state@next", values) == reference(old, es, ds, 6))
    }
    f.checkEdges()
  }
  it should "merge path conditions with an exactly shared hold prefix" in {
    val f = chain(6, nested = true)
    assert(ComposeMaskedUpdates.run(f.graph(states = Set("state")), enabled = true).applied == 1)
    for (es <- 0 until 64; paths <- 0 until 64) {
      val ds = (es * 17 + paths * 3) & 63
      val values = (0 until 6).flatMap(i => Seq(s"e$i" -> BigInt((es >> i) & 1),
        s"p$i" -> BigInt((paths >> i) & 1), s"d$i" -> BigInt((ds >> i) & 1))).toMap +
        ("state" -> BigInt(es & 1))
      assert(f.evaluate("state@next", values) == reference(es & 1, es, ds, 6, paths))
    }
    f.checkEdges()
  }
  it should "retain data and enables that transitively depend on earlier updates" in {
    for (dependentEnable <- Seq(false, true); alias <- Seq(false, true)) {
      val f = chain(6)
      val root = f.producers("state@next").head
      val source = if (alias) {
        f.producers("stage3_alias") = f.producers("stage3").clone()
        f.widths("stage3_alias") = 1
        "stage3_alias"
      } else "stage3"
      f.add("xor", "dependent", 1, source, "1")
      val index = if (dependentEnable) 0 else 1
      val previous = if (dependentEnable) "e5" else "d5"
      f.ops(root)(previous) -= index
      f.ops(root).remove(previous)
      f.users(previous) -= root
      f.ops(root)("dependent") = scala.collection.mutable.HashSet(index)
      f.users.getOrElseUpdate("dependent", scala.collection.mutable.HashSet.empty) += root
      val text = new java.io.StringWriter
      val writer = new java.io.PrintWriter(text)
      assert(ComposeMaskedUpdates.run(f.graph(states = Set("state")), enabled = true,
        report = Some(writer)).applied == 0)
      writer.flush()
      assert(text.toString.contains("depends-on-previous-update"))
      f.checkEdges()
    }
  }
  it should "allow old-state leaves as explicit independent inputs" in {
    val f = chain(6)
    f.add("xor", "old_data", 1, "state", "1")
    val root = f.producers("state@next").head
    f.ops(root).remove("d5"); f.users("d5") -= root
    f.ops(root)("old_data") = scala.collection.mutable.HashSet(1)
    f.users.getOrElseUpdate("old_data", scala.collection.mutable.HashSet.empty) += root
    assert(ComposeMaskedUpdates.run(f.graph(states = Set("state")), enabled = true).applied == 1)
    for (es <- 0 until 64; old <- 0 to 1) {
      val values = (0 until 6).flatMap(i => Seq(s"e$i" -> BigInt((es >> i) & 1),
        s"d$i" -> BigInt(i & 1))).toMap + ("state" -> BigInt(old))
      val ds = 10 | ((old ^ 1) << 5)
      assert(f.evaluate("state@next", values) == reference(old, es, ds, 6))
    }
    f.checkEdges()
  }
  it should "refuse independent-input proofs across actual chain lookup operations" in {
    val f = chain(6)
    f.input("selector", 1)
    f.add("chain", "lookup_data", 1, "selector", "1", "0")
    val root = f.producers("state@next").head
    f.ops(root).remove("d5"); f.users("d5") -= root
    f.ops(root)("lookup_data") = scala.collection.mutable.HashSet(1)
    f.users.getOrElseUpdate("lookup_data", scala.collection.mutable.HashSet.empty) += root
    val text = new java.io.StringWriter; val writer = new java.io.PrintWriter(text)
    assert(ComposeMaskedUpdates.run(f.graph(states = Set("state")), enabled = true,
      report = Some(writer)).applied == 0)
    writer.flush()
    assert(text.toString.contains("opaque-update-input"))
    f.checkEdges()
  }
  it should "leave mismatched hold states and budget exits untouched" in {
    val f = chain(6)
    val before = f.ops.toString
    assert(ComposeMaskedUpdates.run(f.graph(states = Set("state")), enabled = true,
      budget = Budget(maxAdded = 0)).applied == 0)
    assert(f.ops.toString == before)
    val other = new ProjectionFixture
    other.input("state", 1); other.input("other", 1); other.input("e", 1); other.input("d", 1)
    other.add("mux", "state@next", 1, "e", "d", "other")
    assert(ComposeMaskedUpdates.run(other.graph(states = Set("state", "other")), enabled = true).applied == 0)
  }
  it should "spend a bounded candidate count on the deepest update before short names" in {
    val f = chain(6)
    f.input("idle", 1)
    f.add("assign", "idle@next", 1, "idle")
    val untouched = f.producers("idle@next").head
    val stats = ComposeMaskedUpdates.run(f.graph(states = Set("state", "idle")),
      enabled = true, budget = Budget(maxCandidates = 1))
    assert(stats.candidates == 1 && stats.applied == 1)
    assert(f.ops.contains(untouched))
    f.checkEdges()
  }
  it should "compose summaries associatively while preserving their order" in {
    val f = new ProjectionFixture
    val a = new Analysis(f.graph()); val c = new Composer(a); val p = a.pool
    def eval(id: Int): BigInt = {
      val e = p(id)
      e.kind match {
        case "const" => e.value
        case "or" => eval(e.args(0)) | eval(e.args(1))
        case "mux" => if (eval(e.args(0)) != 0) eval(e.args(1)) else eval(e.args(2))
      }
    }
    for (encoded <- 0 until 64) {
      val us = (0 until 3).map(i => Update(p.const((encoded >> (i*2)) & 1, 1),
        p.const((encoded >> (i*2+1)) & 1, 1)))
      val left = c.combine(c.combine(us(0), us(1)), us(2))
      val right = c.combine(us(0), c.combine(us(1), us(2)))
      assert(eval(left.enable) == eval(right.enable))
      if (eval(left.enable) != 0) assert(eval(left.data) == eval(right.data))
    }
  }
  it should "produce a bounded dry-run report without applying projection candidates" in {
    val f = new ProjectionFixture
    f.input("a", 8); f.input("b", 8)
    f.add("cat", "word", 16, "a", "b", "8")
    f.add("and", "out", 8, "word", "255")
    val before = f.ops.toString
    val text = new java.io.StringWriter; val writer = new java.io.PrintWriter(text)
    assert(ProjectSlices.run(f.graph(), enabled = false, report = Some(writer)).candidates == 1)
    writer.flush()
    val row = ujson.read(text.toString.trim)
    assert(row("original_dependencies").arr.nonEmpty)
    assert(row("projected_dependencies").arr.map(_.str) == Seq("b"))
    assert(row("net_operators").num <= 0)
    assert(f.ops.toString == before)
  }
}
