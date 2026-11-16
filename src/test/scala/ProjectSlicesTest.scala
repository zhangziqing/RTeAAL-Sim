package essent

import essent.SliceGraph._
import essent.ProjectSlices._
import org.scalatest.flatspec.AnyFlatSpec
import scala.collection.mutable.{HashMap, HashSet}

private[essent] class ProjectionFixture {
  val ops = HashMap.empty[String, HashMap[String, HashSet[Int]]]
  val users, producers = HashMap.empty[String, HashSet[String]]
  val outputs = HashMap.empty[String, String]
  val widths = HashMap.empty[String, Int]
  def input(s: String, w: Int): String = { widths(s) = w; s }
  def add(k: String, out: String, w: Int, in: String*): String = {
    val op = s"${k}_+_${ops.size}"
    ops(op) = HashMap.empty
    in.zipWithIndex.foreach { case (s, i) =>
      ops(op).getOrElseUpdate(s, HashSet.empty) += i
      users.getOrElseUpdate(s, HashSet.empty) += op
      if (number(s).nonEmpty) widths.getOrElseUpdate(s, 64)
    }
    outputs(op) = out; widths(op) = w; widths(out) = w; producers(out) = HashSet(op)
    out
  }
  def graph(protectedNames: Set[String] = Set.empty, states: Set[String] = Set.empty): Graph =
    new Graph(ops, users, producers, outputs, widths, protectedNames, states)
  def evaluate(out: String, values: Map[String, BigInt]): BigInt = {
    val known = HashMap.from(values)
    def eval(s: String): BigInt = number(s).getOrElse(known.getOrElseUpdate(s, {
      val g = graph(); val op = g.producer(s).get
      val in = g.ordered(op).map(eval)
      g.kind(op) match {
        case "assign" => in(0)
        case "cat" => (in(0) << in(2).toInt) | in(1)
        case "catn" => (0 until in(0).toInt).foldLeft(BigInt(0))((v, i) => v | (in(1 + i*2) << in(2 + i*2).toInt))
        case "bits" => (in(0) >> in(1).toInt) & in(2)
        case "and" => in(0) & in(1)
        case "or" => in(0) | in(1)
        case "xor" => in(0) ^ in(1)
        case "not" => ~in(0) & mask(widths(s))
        case "mux" => if (in(0) != 0) in(1) else in(2)
        case "add" => (in(1) + in(2)) & mask(widths(s))
        case "shl" => in(0) << in(1).toInt
        case "shr" => in(0) >> in(1).toInt
        case other => throw new IllegalArgumentException(other)
      }
    }))
    eval(out)
  }
  def checkEdges(): Unit = {
    ops.foreach { case (op, in) =>
      assert(producers(outputs(op))(op))
      assert(widths(op) == widths(outputs(op)))
      in.keys.foreach(s => assert(users(s)(op)))
    }
    users.foreach { case (s, us) => us.foreach(op => assert(ops(op).contains(s))) }
    producers.values.foreach(_.foreach(op => assert(ops.contains(op))))
  }
}

class ProjectSlicesTest extends AnyFlatSpec {
  behavior of "ProjectSlices"
  it should "project crossing binary and variadic fields including repeated operands" in {
    for (variadic <- Seq(false, true)) {
      val f = new ProjectionFixture
      f.input("x", 8); f.input("y", 8)
      if (variadic) f.add("catn", "cat", 24, "3", "x", "16", "y", "8", "x", "0")
      else { f.add("cat", "xy", 16, "x", "y", "8"); f.add("cat", "cat", 24, "xy", "x", "8") }
      f.add("bits", "out", 10, "cat", "6", "1023")
      assert(ProjectSlices.run(f.graph(), enabled = true).applied > 0)
      for (x <- 0 until 256 by 7; y <- 0 until 256 by 13) {
        val v = Map("x" -> BigInt(x), "y" -> BigInt(y))
        assert(f.evaluate("out", v) == (((BigInt(x) << 16) | (BigInt(y) << 8) | x) >> 6 & 1023))
      }
      f.checkEdges()
    }
  }
  it should "merge nested slices and extractor low masks while retaining shared whole consumers" in {
    val f = new ProjectionFixture
    f.input("a", 16); f.input("b", 16)
    f.add("cat", "word", 32, "a", "b", "16")
    f.add("bits", "slice", 16, "word", "8", "65535")
    f.add("and", "out", 8, "slice", "255")
    f.add("assign", "observed", 32, "word")
    ProjectSlices.run(f.graph(Set("observed")), enabled = true)
    for (x <- Seq(0, 1, 32768, 65535); y <- Seq(0, 1, 32768, 65535)) {
      val v = Map("a" -> BigInt(x), "b" -> BigInt(y))
      assert(f.evaluate("out", v) == ((y >> 8) & 255))
      assert(f.evaluate("observed", v) == ((BigInt(x) << 16) | y))
    }
    assert(f.producers.contains("word")); f.checkEdges()
  }
  it should "drop a mux condition only when the requested branches are identical" in {
    for (same <- Seq(false, true)) {
      val f = new ProjectionFixture
      f.input("x", 8); f.input("y", 8); f.input("z", 8); f.input("c", 1)
      f.add("cat", "left", 16, "x", "y", "8")
      f.add("cat", "right", 16, "z", if (same) "y" else "x", "8")
      f.add("mux", "m", 16, "c", "left", "right")
      f.add("and", "out", 8, "m", "255")
      val a = new Analysis(f.graph())
      val id = a.request(Slice("m", 0, 8)).toOption.get
      assert(a.pool.references(id)("c") != same)
      ProjectSlices.run(f.graph(), enabled = true)
      for (c <- 0 to 1) assert(f.evaluate("out", Map("c" -> BigInt(c), "x" -> BigInt(12),
        "y" -> BigInt(53), "z" -> BigInt(91))) == (if (same || c == 1) 53 else 12))
      f.checkEdges()
    }
  }
  it should "respect 1 31 32 63 and 64 bit boundaries with explicit masks" in {
    for (w <- Seq(1, 31, 32, 63, 64)) {
      val f = new ProjectionFixture
      f.input("x", 64); f.input("y", 64)
      f.add("xor", "word", 64, "x", "y")
      val shift = 64 - w
      f.add("bits", "out", w, "word", shift.toString, mask(w).toString)
      ProjectSlices.run(f.graph(), enabled = true)
      val random = new scala.util.Random(w)
      for (_ <- 0 until 100) {
        val x = BigInt(64, random); val y = BigInt(64, random)
        assert(f.evaluate("out", Map("x" -> x, "y" -> y)) == ((x ^ y) >> shift & mask(w)))
      }
      f.checkEdges()
    }
  }
  it should "leave arithmetic dynamic shifts memory and lookup boundaries as explicit inputs" in {
    for (kind <- Seq("add", "shl", "memr", "lookup", "chain")) {
      val f = new ProjectionFixture
      f.input("x", 32); f.input("y", 32)
      f.add(kind, "word", 32, "x", "y")
      val a = new Analysis(f.graph())
      val id = a.request(Slice("word", 3, 8)).toOption.get
      assert(a.pool(id) == Expr("ref", Vector.empty, 8, "word", 3))
    }
  }
  it should "preserve actual chain lookup identities when projected branches remove their use" in {
    val f = new ProjectionFixture
    f.input("selector", 1); f.input("x", 8); f.input("y", 8); f.input("z", 8)
    f.add("chain", "condition", 1, "selector", "1", "0")
    val lookup = f.producers("condition").head
    f.add("cat", "left", 16, "y", "x", "8")
    f.add("cat", "right", 16, "z", "x", "8")
    f.add("mux", "word", 16, "condition", "left", "right")
    f.add("and", "out", 8, "word", "255")
    assert(!f.graph().removable(lookup))
    assert(ProjectSlices.run(f.graph(), enabled = true).applied > 0)
    assert(f.ops.contains(lookup) && f.producers("condition")(lookup))
    assert(f.evaluate("out", Map("x" -> BigInt(53))) == 53)
    f.checkEdges()
  }
  it should "reject unknown widths budgets and aliased roots without changing the graph" in {
    val f = new ProjectionFixture
    f.input("x", 8); f.input("y", 8)
    f.add("cat", "word", 16, "x", "y", "8")
    f.add("and", "out", 8, "word", "255")
    val a = new Analysis(f.graph(), budget = Budget(maxVisits = 1))
    assert(a.request(Slice("word", 0, 8)) == Left("analysis-budget"))
    assert(a.request(Slice("missing", 0, 8)) == Left("unknown-wide-or-invalid-width"))
    val before = f.ops.toString
    assert(ProjectSlices.run(f.graph(), enabled = true, budget = Budget(maxAdded = 0)).applied == 0)
    assert(f.ops.toString == before)
    f.producers("alias") = f.producers("out").clone(); f.widths("alias") = 8
    assert(ProjectSlices.run(f.graph(), enabled = true).applied == 0)
    f.checkEdges()
  }
  it should "include the final assignment in whole-reference depth and growth decisions" in {
    val f = new ProjectionFixture
    f.input("x", 8)
    f.add("assign", "producer", 8, "x")
    f.add("assign", "out", 8, "x")
    val g = f.graph()
    val pool = new Pool
    val root = f.producers("out").head
    val p = new SliceRewrite.Rewriter(g, pool, Budget()).plan(root, pool.ref("producer", 0, 8))
    assert(p.before == 1 && p.after == 2 && p.reason == "no-depth-benefit")
    assert(p.operations.size == 1 && p.operations.head.inputs == Vector("producer"))
  }
}
