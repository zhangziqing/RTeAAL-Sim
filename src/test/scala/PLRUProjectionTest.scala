package essent

import essent.SliceGraph.Graph
import firrtl._
import firrtl.ir._
import org.scalatest.flatspec.AnyFlatSpec

import java.nio.file.{Files, Paths}
import scala.collection.mutable

/** Integration fixture comes from the pinned Nanhu artifact, retaining the
  * original six-update expressions. It is deliberately not a PLRU generator.
  */
class PLRUProjectionTest extends AnyFlatSpec {
  private val old = "normal_refill_idx_state_reg"
  private val next = old + "@next"
  private val sourcePaths = Seq(Paths.get("../results/nanhu/SimTop.preclock.lo.fir"),
    Paths.get("results/nanhu/SimTop.preclock.lo.fir"))
  private lazy val actual = extractedCircuit()

  private def extractedCircuit(): Circuit = {
    val source = sourcePaths.find(Files.isRegularFile(_))
    assume(source.nonEmpty, "Pinned Nanhu preclock FIRRTL is unavailable; actual-cone check not run")
    val reader = scala.io.Source.fromFile(source.get.toFile)
    val selected = mutable.ArrayBuffer.empty[String]
    var update: Option[String] = None
    try reader.getLines().foreach { line =>
      val text = line.trim
      if (text.startsWith("node normal_refill_idx_") || text.startsWith("node _normal_refill_idx_"))
        selected += line
      if (text.startsWith(old + " <= ")) update = Some(text.stripPrefix(old + " <= "))
    } finally reader.close()
    assert(update.contains("mux(_normal_refill_idx_T_4, _normal_refill_idx_state_reg_T_647, " + old + ")"),
      "The actual-cone fixture changed; recheck its six-update and state-layout contract")
    assert(selected.exists(_.contains("node _normal_refill_idx_state_reg_T_647 =")))
    def rename(text: String): String = (0 until 6).foldLeft(text) { (s, i) =>
      s.replace(s"normalPage_tlb_normal_fa.io_access_${i}_touch_ways_bits", s"way$i")
        .replace(s"normalPage_tlb_normal_fa.io_access_${i}_touch_ways_valid", s"valid$i")
    }
    val ports = (0 until 6).map(i => s"    input way$i : UInt<5>\n    input valid$i : UInt<1>").mkString("\n")
    val text = s"""circuit ActualPLRU32 :
  module ActualPLRU32 :
    input $old : UInt<31>
    input reset : UInt<1>
    input update_enable : UInt<1>
$ports
    output next_state : UInt<31>
${selected.map(rename).mkString("\n")}
    node actual_update = ${rename(update.get)}
    node enabled_update = mux(update_enable, actual_update, $old)
    next_state <= mux(reset, UInt<31>(0), enabled_update)
"""
    val parsed = Parser.parse(text)
    val compiler = new firrtl.stage.transforms.Compiler(firrtl.stage.Forms.LowFormOptimized)
    val result = compiler.execute(CircuitState(parsed, Seq.empty)).circuit
    firrtl.passes.CheckTypes.run(result)
    firrtl.passes.CheckWidths.run(result)
    result
  }

  private def extract(circuit: Circuit): Graph = {
    val module = circuit.modules.head.asInstanceOf[Module]
    val statements = module.body match { case b: Block => b.stmts; case s => Seq(s) }
    val te = new TeAALExtractor(mutable.LinkedHashMap.empty)
    module.ports.foreach(p => te.extractMetadata(p.tpe, p.name, false))
    StatementGraph(statements).stmtsOrdered().foreach(te.extractStmt)
    BalanceConcatOps.run(te.opInBufferOrder, te.inEdgeBuffer, te.outEdgeBuffer,
      te.oEBufferR, te.bitWidthMetadata, Set("next_state"))
    val root = te.outEdgeBuffer.remove("next_state").get
    te.outEdgeBuffer(next) = root
    root.foreach(op => te.oEBufferR(op) = next)
    te.bitWidthMetadata(next) = 31
    new Graph(te.opInBufferOrder, te.inEdgeBuffer, te.outEdgeBuffer,
      te.oEBufferR, te.bitWidthMetadata, Set(next), Set(old))
  }

  // Independent path model: each subtree stores its root above two equal-size
  // child states; high way digits choose the high child, low digits the low.
  // A touch marks the opposite child older and never reads prior path updates.
  private def reference(previous: BigInt, ways: Seq[Int], valid: Int,
                        reset: Boolean, enabled: Boolean): BigInt = {
    if (reset) return BigInt(0)
    if (!enabled) return previous
    var result = previous
    ways.zipWithIndex.foreach { case (way, port) =>
      if ((valid & (1 << port)) != 0) {
        var base = 0
        for (level <- 4 to 0 by -1) {
          val direction = (way >> level) & 1
          val position = base + (1 << (level + 1)) - 2
          result = if (direction == 0) result.setBit(position) else result.clearBit(position)
          if (direction == 1) base += (1 << level) - 1
        }
      }
    }
    result
  }

  private def inputs(previous: BigInt, ways: Seq[Int], valid: Int,
                     reset: Boolean, enabled: Boolean): Map[String, BigInt] =
    ways.zipWithIndex.flatMap { case (way, i) => Seq(s"way$i" -> BigInt(way),
      s"valid$i" -> BigInt((valid >> i) & 1)) }.toMap ++ Map(old -> previous,
      "reset" -> BigInt(if (reset) 1 else 0), "update_enable" -> BigInt(if (enabled) 1 else 0))

  /** Independent unsigned tensor evaluator, compiled from production layers.
    * Count/shift/mask operands follow the runtime ABI rather than FIRRTL syntax.
    */
  private class Execution(graph: Graph) {
    private val root = graph.producer(next).get
    private val df = new TeAALDFGraphExtractor(graph.ops, graph.users, graph.producers,
      graph.outputs, graph.widths, mutable.HashSet(old), mutable.HashSet.empty,
      mutable.ArrayBuffer.empty, mutable.HashSet.empty, mutable.HashMap.empty,
      mutable.HashMap.empty)
    df.opGraphConstructor(graph.users, graph.producers)
    private val ins = mutable.HashMap.from(df.inNeigh.toSeq.map { case (k, v) => k -> v.clone() })
    private val outs = mutable.HashMap.from(df.outNeigh.toSeq.map { case (k, v) => k -> v.clone() })
    df.layerExtract(outs, ins, graph.users, graph.producers)
    val depth: Int = df.nodeToLayer(root) + 1
    val layers: Int = df.LAYER_NUM
    private val ordered = (0 until layers).flatMap(i => df.layerMap(s"layer$i").toSeq.sorted).toVector
    assert(ordered.toSet == graph.ops.keySet.toSet)
    private val slots = mutable.HashMap.empty[String, Int]
    private val constants = mutable.ArrayBuffer.empty[(Int, BigInt)]
    private val initial = mutable.HashMap.empty[String, Int]
    private def allocate(name: String): Int = slots.getOrElseUpdate(name, {
      val idx = slots.size
      if (name.matches("-?[0-9]+")) constants += idx -> BigInt(name)
      else if (name.startsWith("UInt<")) {
        val hex = name.substring(name.indexOf('h') + 1, name.lastIndexOf('"'))
        constants += idx -> BigInt(hex, 16)
      } else {
        assert(!graph.ops.contains(name), s"Layer consumes an unavailable producer: $name")
        initial(name) = idx
      }
      idx
    })
    private case class Instruction(kind: String, args: Vector[Int], output: Int, width: Int)
    private val code = ordered.map { op =>
      val args = graph.ordered(op).map(allocate)
      val output = slots.size
      assert(!slots.contains(op))
      slots(op) = output
      Instruction(graph.kind(op), args, output, graph.widths(op))
    }
    private val result = slots(root)
    def apply(input: Map[String, BigInt]): BigInt = {
      val values = Array.fill[BigInt](slots.size)(BigInt(0))
      constants.foreach { case (i, value) => values(i) = value }
      initial.foreach { case (name, i) => values(i) = input(name) }
      code.foreach { instruction =>
        val args = instruction.args.map(values)
        val raw = instruction.kind match {
          case "assign" => args(0)
          case "and" => args(0) & args(1)
          case "or" => args(0) | args(1)
          case "xor" => args(0) ^ args(1)
          case "bits" => (args(0) >> args(1).toInt) & args(2)
          case "mux" => if (args(0) != 0) args(1) else args(2)
          case "cat" => (args(0) << args(2).toInt) | args(1)
          case "catn" => (0 until args(0).toInt).foldLeft(BigInt(0)) { (acc, i) =>
            acc | (args(1 + 2 * i) << args(2 + 2 * i).toInt)
          }
          case "shl" => args(0) << args(1).toInt
          case "shr" => args(0) >> args(1).toInt
          case other => fail(s"Unexpected operation in actual PLRU cone: $other")
        }
        values(instruction.output) = raw & ((BigInt(1) << instruction.width) - 1)
      }
      values(result)
    }
  }

  private def verify(executions: Seq[(String, Execution)]): Unit = {
    val patterns = (0 until 32).map(j => Seq(j, j, j ^ 16, j ^ 1, (j + 7) & 31, 31 - j)) ++
      Seq(Seq.fill(6)(0), Seq.fill(6)(31), Seq(0, 31, 0, 31, 0, 31))
    val random = new scala.util.Random(1791)
    for (ways <- patterns; valid <- 0 until 64; reset <- Seq(false, true); enabled <- Seq(false, true)) {
      val previous = if (valid == 63) BigInt(0) else if (valid == 0) (BigInt(1) << 31) - 1
        else BigInt(31, random)
      val expected = reference(previous, ways, valid, reset, enabled)
      val input = inputs(previous, ways, valid, reset, enabled)
      executions.foreach { case (variant, execute) =>
        assert(execute(input) == expected,
          s"variant=$variant ways=$ways valid=$valid reset=$reset enabled=$enabled previous=$previous")
      }
    }
  }

  "Actual 32-way PLRU" should "match the independent path model for all six-port valid masks" in {
    val baseline = new Execution(extract(actual))
    verify(Seq("A" -> baseline))
    info(s"Actual extracted PLRU baseline: ${baseline.depth} value layers, ${baseline.layers} graph layers")
  }

  it should "preserve projection and ordered update composition through production layering" in {
    val baseline = new Execution(extract(actual))
    val projected = extract(actual)
    val projectionStats = ProjectSlices.run(projected, enabled = true)
    val projection = new Execution(projected)
    val combined = extract(actual)
    ProjectSlices.run(combined, enabled = true)
    val reportText = new java.io.StringWriter
    val report = new java.io.PrintWriter(reportText)
    val compositionStats = ComposeMaskedUpdates.run(combined, enabled = true, report = Some(report))
    report.flush()
    val composition = new Execution(combined)
    verify(Seq("B" -> projection, "C" -> composition))
    info(s"Actual PLRU value layers A/B/C: ${baseline.depth}/${projection.depth}/${composition.depth}")
    info(s"Projection: $projectionStats; composition: $compositionStats")
    info(reportText.toString)
    assert(projection.depth < baseline.depth, "Actual-cone projection must shorten the update path")
    assert(composition.depth < projection.depth, "Actual-cone summaries must survive extraction and layering")
  }
}
