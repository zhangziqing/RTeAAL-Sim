package essent

import essent.SliceGraph._
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Demand-driven bit provenance. No graph mutation takes place during analysis. */
object ProjectSlices {
  case class Budget(maxVisits: Int = 2048, maxCache: Int = 200000,
                    maxAdded: Int = 2048, maxGrowth: Int = 64, maxTotalGrowth: Int = 8192,
                    maxCandidates: Int = 20000)
  case class Slice(signal: String, lo: Int, width: Int)
  case class Limit(reason: String) extends RuntimeException(reason)
  case class Stats(candidates: Int = 0, applied: Int = 0, added: Int = 0, removed: Int = 0)

  /** Only fragmented register updates are split into fields. Ordinary register
    * arithmetic is never expanded bit by bit, even when its depth is large.
    */
  def stateCandidates(graph: Graph): Vector[String] = graph.outputs.iterator.collect {
    case (op, out) if out.endsWith("@next") && graph.width(out) > 1 && graph.width(out) <= 64 &&
        graph.states(out.stripSuffix("@next")) => op
  }.filter { root =>
    val seen = HashSet.empty[String]
    val work = ArrayBuffer(graph.outputs(root))
    var cats = 0; var muxes = 0; var old = false
    val state = graph.outputs(root).stripSuffix("@next")
    while (work.nonEmpty && seen.size < 2048 && !(old && cats >= 1 && muxes >= 2)) {
      val s = work.remove(work.size - 1)
      if (s == state) old = true
      else if (seen.add(s)) graph.producer(s).foreach { op =>
        graph.kind(op) match {
          case "cat" | "catn" => cats += 1; work ++= graph.ordered(op).filter(n => number(n).isEmpty)
          case "mux" => muxes += 1; work ++= graph.ordered(op).drop(1)
          case "bits" | "and" | "assign" => work ++= graph.ordered(op).filter(n => number(n).isEmpty)
          case _ =>
        }
      }
    }
    old && cats >= 1 && muxes >= 2
  }.toVector.sorted

  def reportCandidate(report: Option[java.io.PrintWriter], stage: String, graph: Graph,
      root: String, slice: Option[Slice], pool: Pool, expr: Option[Int],
      plan: Option[SliceRewrite.Plan], reason: String): Unit = report.foreach { writer =>
    val row = ujson.Obj("stage" -> stage, "operation" -> root, "output" -> graph.outputs(root),
      "original_dependencies" -> ujson.Arr.from(graph.ops(root).keys.toVector.sorted),
      "projected_dependencies" -> ujson.Arr.from(expr.toVector.flatMap(pool.references).distinct.sorted),
      "reason" -> reason)
    slice.foreach(s => row("slice") = ujson.Obj("signal" -> s.signal, "start" -> s.lo, "width" -> s.width))
    plan.foreach { p =>
      row("original_depth") = p.before; row("projected_depth") = p.after
      row("added_operators") = p.operations.size; row("removed_operators") = p.removed.size
      row("net_operators") = p.delta; row("shared_nodes") = ujson.Arr.from(p.shared)
    }
    writer.println(ujson.write(row))
  }

  def run(graph: Graph, enabled: Boolean, report: Option[java.io.PrintWriter] = None,
          budget: Budget = Budget()): Stats = {
    val analysis = new Analysis(graph, budget = budget)
    val rewriter = new SliceRewrite.Rewriter(graph, analysis.pool, budget)
    val states = stateCandidates(graph).toSet
    val slices = graph.ops.keysIterator.filter(op => analysis.sliceConsumer(op).nonEmpty).toVector
    val roots = (states.toVector ++ slices.filterNot(states)).distinct
      .sortBy(op => (-graph.depth(graph.outputs(op)), op)).take(budget.maxCandidates)
    var stats = Stats()
    val deferred = ArrayBuffer.empty[String]
    def visit(op: String, allowGrowth: Boolean): Unit = if (graph.ops.contains(op)) {
      val slice = analysis.sliceConsumer(op)
      val result = if (states(op)) {
        val out = graph.outputs(op); val w = graph.width(out)
        val bits = (0 until w).reverse.map(i => analysis.request(Slice(out, i, 1))).toVector
        bits.collectFirst { case Left(reason) => reason } match {
          case Some(reason) => Left(reason)
          case None => Right(analysis.pool.op("catn", bits.collect { case Right(id) => id }, w))
        }
      } else analysis.request(slice.get)
      result match {
        case Left(reason) =>
          stats = stats.copy(candidates = stats.candidates + 1)
          reportCandidate(report, "projection", graph, op, slice, analysis.pool, None, None, reason)
        case Right(expr) =>
          val plan = rewriter.plan(op, expr)
          if (enabled && !allowGrowth && plan.operations.nonEmpty && plan.delta > 0) {
            deferred += op
            return
          }
          stats = stats.copy(candidates = stats.candidates + 1)
          reportCandidate(report, "projection", graph, op, slice, analysis.pool, Some(expr), Some(plan), plan.reason)
          if (enabled && plan.accepted) {
            rewriter.commit(plan)
            analysis.clear()
            stats = stats.copy(applied = stats.applied + 1, added = stats.added + plan.operations.size,
              removed = stats.removed + plan.removed.size)
          }
      }
    }
    roots.foreach(visit(_, allowGrowth = false))
    deferred.foreach(visit(_, allowGrowth = true))
    stats
  }

  class Analysis(val graph: Graph, val pool: Pool = new Pool, val budget: Budget = Budget()) {
    val cache = HashMap.empty[Slice, Int]
    val boundaries = HashSet.empty[String]
    private val active = HashSet.empty[Slice]
    private var visits = 0
    def request(s: Slice): Either[String, Int] = {
      visits = 0
      boundaries.clear()
      try Right(project(s.signal, s.lo, s.width)) catch { case Limit(reason) => Left(reason) }
    }
    def clear(): Unit = { cache.clear(); active.clear() }
    private def constant(s: String): Option[BigInt] = number(s)
    def lowMask(s: String, w: Int): Boolean = constant(s).contains(mask(w))
    def sliceConsumer(op: String): Option[Slice] = {
      val ins = graph.ordered(op)
      val w = graph.width(graph.outputs.getOrElse(op, ""))
      if (w < 1 || w > 64) None
      else graph.kind(op) match {
        case "bits" if ins.size == 3 && ins(1).toIntOption.exists(_ >= 0) && lowMask(ins(2), w) =>
          Some(Slice(ins(0), ins(1).toInt, w))
        case "and" if ins.size == 2 && lowMask(ins(1), w) && graph.width(ins(0)) >= w =>
          Some(Slice(ins(0), 0, w))
        case "and" if ins.size == 2 && lowMask(ins(0), w) && graph.width(ins(1)) >= w =>
          Some(Slice(ins(1), 0, w))
        case _ => None
      }
    }
    private def leaf(s: String, lo: Int, w: Int, reason: String): Int = {
      boundaries += reason
      pool.ref(s, lo, w)
    }
    private def project(s: String, lo: Int, w: Int): Int = {
      val key = Slice(s, lo, w)
      cache.get(key) match { case Some(id) => return id; case _ => }
      visits += 1
      if (visits > budget.maxVisits || cache.size >= budget.maxCache || active.size >= 192)
        throw Limit("analysis-budget")
      val sw = graph.width(s)
      if (w < 1 || w > 64 || lo < 0 || sw < 1 || sw > 64 || lo.toLong + w > sw)
        throw Limit("unknown-wide-or-invalid-width")
      if (!active.add(key)) throw Limit("cyclic-provenance")
      val result = try constant(s) match {
        case Some(v) => pool.const(v >> lo, w)
        case None => graph.producer(s) match {
          case None => leaf(s, lo, w, "cycle-input")
          case Some(op) =>
            val in = graph.ordered(op)
            val k = graph.kind(op)
            def sub(i: Int): Int = project(in(i), lo, w)
            if (graph.protectedNames(op) || Set("memr", "memw", "lookup", "chain")(k))
              leaf(s, lo, w, "protected-memory-or-lookup")
            else if (k == "assign" && in.size == 1 && graph.width(in.head) == sw)
              project(in.head, lo, w)
            else if (sliceConsumer(op).nonEmpty) {
              val slice = sliceConsumer(op).get
              project(slice.signal, slice.lo + lo, w)
            } else if (lo == 0 && w == sw)
              leaf(s, lo, w, "whole-value")
            else k match {
              case "cat" | "catn" =>
                val fields = if (k == "cat" && in.size == 3 &&
                    in(2).toIntOption.contains(graph.width(in(1))))
                  Vector(in(0) -> graph.width(in(1)), in(1) -> 0)
                else if (k == "catn" && in.headOption.flatMap(_.toIntOption).exists(n =>
                    n >= 1 && n <= 64 && in.size == 1 + 2 * n) &&
                    in.indices.drop(2).by(2).forall(i => in(i).toIntOption.nonEmpty))
                  in.drop(1).grouped(2).map(p => p(0) -> p(1).toInt).toVector
                else Vector.empty
                val sorted = fields.sortBy(_._2)
                val valid = sorted.nonEmpty && sorted.head._2 == 0 &&
                  sorted.forall(p => graph.width(p._1) > 0) &&
                  sorted.sliding(2).forall(p => p.size < 2 || p(0)._2 + graph.width(p(0)._1) == p(1)._2) &&
                  sorted.last._2 + graph.width(sorted.last._1) == sw
                if (!valid) leaf(s, lo, w, "invalid-concat-layout")
                else {
                  val parts = fields.sortBy(-_._2).flatMap { case (signal, offset) =>
                    val start = lo.max(offset)
                    val end = (lo + w).min(offset + graph.width(signal))
                    if (start < end) Some(project(signal, start - offset, end - start)) else None
                  }
                  pool.op("catn", parts, w)
                }
              case "mux" if in.size == 3 && graph.width(in.head) == 1 &&
                  in.drop(1).forall(n => graph.width(n) >= lo + w) =>
                val t = sub(1); val f = sub(2)
                if (t == f) t else pool.op("mux", Vector(project(in.head, 0, 1), t, f), w)
              case "and" | "or" | "xor" if in.size == 2 &&
                  in.forall(n => constant(n).nonEmpty || graph.width(n) >= lo + w) =>
                def bitOperand(i: Int): Int = constant(in(i)) match {
                  case Some(v) => pool.const(v >> lo, w)
                  case None => sub(i)
                }
                pool.op(k, Vector(bitOperand(0), bitOperand(1)), w)
              case "not" if in.size == 1 && graph.width(in.head) >= lo + w =>
                pool.op("xor", Vector(sub(0), pool.const(mask(w), w)), w)
              case _ => leaf(s, lo, w, "arithmetic-shift-or-unsupported:" + k)
            }
        }
      } finally active -= key
      cache(key) = result
      result
    }
  }
}
