package essent

import essent.SliceGraph._
import essent.ProjectSlices.{Analysis, Budget, Limit, Slice, Stats, reportCandidate}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Compose ordered independent overwrites. The old register is a cycle input;
  * no update, reset, or commit event is moved across a register boundary.
  */
object ComposeMaskedUpdates {
  case class Update(enable: Int, data: Int)
  class Composer(val analysis: Analysis) {
    val graph = analysis.graph
    val pool = analysis.pool
    private def bitAnd(a: Int, b: Int): Int = pool.op("and", Vector(a, b), 1)
    private def invert(a: Int): Int = pool.op("xor", Vector(a, pool.const(1, 1)), 1)
    def combine(a: Update, b: Update): Update = Update(
      pool.op("or", Vector(a.enable, b.enable), 1),
      pool.op("mux", Vector(b.enable, b.data, a.data), pool(a.data).width))

    /** Prove each hold path reaches this exact state bit. Shared prefixes are
      * previous updates; gate only the differing suffix by the Mux path.
      */
    def updates(root: Int, state: String, bit: Int): Either[String, Vector[Update]] = {
      val base = pool.ref(state, bit, 1)
      val memo = HashMap.empty[Int, Option[Vector[Update]]]
      val expanded = HashMap.empty[Int, Int]
      val visiting = HashSet.empty[Int]
      var steps = 0
      def project(s: String, lo: Int, w: Int): Int = analysis.request(Slice(s, lo, w)) match {
        case Right(id) => id
        case Left(reason) => throw Limit(reason)
      }
      def expand(id: Int): Int = expanded.getOrElseUpdate(id, {
        val e = pool(id)
        if (e.kind != "ref" || graph.states(e.signal)) id
        else graph.producer(e.signal) match {
          case Some(op) if graph.kind(op) == "mux" && !graph.protectedNames(op) =>
            val in = graph.ordered(op)
            if (in.size != 3 || graph.width(in.head) != 1) throw Limit("invalid-mux")
            // Resolve normalization wrappers before interning path conditions
            // so identical update prefixes retain a shared representation.
            pool.op("mux", Vector(project(in.head, 0, 1), project(in(1), e.lo, e.width),
              project(in(2), e.lo, e.width)), e.width)
          case _ => id
        }
      })
      def chain(id: Int): Option[Vector[Update]] = memo.getOrElseUpdate(id, {
        steps += 1
        if (steps > analysis.budget.maxVisits || visiting.size >= 192) throw Limit("summary-budget")
        if (!visiting.add(id)) throw Limit("cyclic-summary")
        val result = if (id == base) Some(Vector.empty)
        else {
          val x = expand(id); val e = pool(x)
          if (x != id) chain(x)
          else if (e.kind != "mux") None
          else {
            val c = e.args(0); val t = e.args(1); val f = e.args(2)
            (chain(t), chain(f)) match {
              case (Some(a), Some(b)) =>
                val n = a.zip(b).takeWhile { case (l, r) => l == r }.size
                Some(a.take(n) ++ a.drop(n).map(u => u.copy(enable = bitAnd(c, u.enable))) ++
                  b.drop(n).map(u => u.copy(enable = bitAnd(invert(c), u.enable))))
              case (None, Some(b)) => Some(b :+ Update(c, t))
              case (Some(a), None) => Some(a :+ Update(invert(c), f))
              case _ => None
            }
          }
        }
        visiting -= id
        if (result.exists(_.size > 64)) throw Limit("too-many-updates")
        result
      })
      try chain(root) match {
        case None => Left("hold-is-not-the-same-state-bit")
        case Some(us) =>
          val priorIds = memo.iterator.collect { case (id, Some(xs)) if xs.nonEmpty => id }.toSet
          val priorSignals = analysis.cache.iterator.collect {
            case (slice, id) if priorIds(id) && slice.signal != state => slice.signal
          }.toSet ++ expanded.iterator.collect {
            case (id, x) if id != x && priorIds(x) => pool(id).signal
          }
          val priorProducers = priorSignals.flatMap(graph.producer)
          def independent(id: Int): Boolean = {
            val reachable = pool.reachable(id)
            if (reachable.exists(priorIds)) return false
            val work = ArrayBuffer.from(pool.references(id))
            val seen = HashSet.empty[String]
            while (work.nonEmpty) {
              if (seen.size >= analysis.budget.maxVisits) throw Limit("dependency-budget")
              val s = work.remove(work.size - 1)
              if (priorSignals(s)) return false
              if (seen.add(s) && !graph.states(s)) graph.producer(s).foreach { op =>
                if (priorProducers(op)) return false
                // Lookup entries are encoded out of band, and memory is a
                // semantic boundary. Refuse a proof that would need either.
                if (Set("lookup", "chain", "memr", "memw")(graph.kind(op))) throw Limit("opaque-update-input")
                work ++= graph.ops(op).keysIterator.filter(n => number(n).isEmpty)
              }
            }
            true
          }
          if (us.forall(u => independent(u.enable) && independent(u.data))) Right(us)
          else Left("depends-on-previous-update")
      } catch { case Limit(reason) => Left(reason) }
    }

    /** Ordered interval DP accounts for actual input arrivals. Six entries are
      * eligible without the unrelated priority-Mux pass's eight-entry cutoff.
      */
    def tree(updates: Vector[Update]): Update = {
      require(updates.nonEmpty)
      val memo = HashMap.empty[(Int, Int), Update]
      def cost(u: Update): (Int, Int) = (
        graph.expressionDepth(pool, u.enable).max(graph.expressionDepth(pool, u.data)),
        (pool.reachable(u.enable).toSet ++ pool.reachable(u.data)).size)
      def best(start: Int, end: Int): Update = memo.getOrElseUpdate(start -> end,
        if (end - start == 1) updates(start)
        else (start + 1 until end).map(mid => combine(best(start, mid), best(mid, end))).minBy(cost))
      best(0, updates.size)
    }
  }

  def run(graph: Graph, enabled: Boolean, report: Option[java.io.PrintWriter] = None,
          budget: Budget = Budget()): Stats = {
    val analysis = new Analysis(graph, budget = budget)
    val pool = analysis.pool
    val composer = new Composer(analysis)
    val rewriter = new SliceRewrite.Rewriter(graph, pool, budget)
    val roots = (ProjectSlices.stateCandidates(graph) ++ graph.outputs.iterator.collect {
      case (op, out) if out.endsWith("@next") && graph.width(out) == 1 &&
        graph.states(out.stripSuffix("@next")) => op
    }).distinct.sortBy(op => (-graph.depth(graph.outputs(op)), op)).take(budget.maxCandidates)
    var stats = Stats()
    roots.foreach { op => if (graph.ops.contains(op)) {
      val out = graph.outputs(op); val w = graph.width(out); val state = out.stripSuffix("@next")
      var reason = ""
      var count = 0
      val summaries = (0 until w).reverse.map { bit =>
        val summary = for {
          expr <- analysis.request(Slice(out, bit, 1))
          us <- composer.updates(expr, state, bit)
        } yield {
          count = count.max(us.size)
          if (us.isEmpty) Update(pool.const(0, 1), pool.const(0, 1)) else composer.tree(us)
        }
        summary match {
          case Right(u) => u
          case Left(r) => reason = r; Update(pool.const(0, 1), pool.const(0, 1))
        }
      }.toVector
      stats = stats.copy(candidates = stats.candidates + 1)
      if (reason.isEmpty && count < 2) reason = "fewer-than-two-independent-updates"
      if (reason.nonEmpty) reportCandidate(report, "composition", graph, op, None, pool, None, None, reason)
      else {
        val bits = summaries.zipWithIndex.map { case (u, i) =>
          pool.op("mux", Vector(u.enable, u.data, pool.ref(state, w - 1 - i, 1)), 1)
        }
        val bitForm = pool.op("catn", bits, w)
        val wordMask = pool.op("catn", summaries.map(_.enable), w)
        val wordData = pool.op("catn", summaries.map(u => pool.op("and", Vector(u.enable, u.data), 1)), w)
        val keepMask = pool.op("xor", Vector(wordMask, pool.const(mask(w), w)), w)
        val wordForm = pool.op("or", Vector(pool.op("and", Vector(pool.ref(state, 0, w), keepMask), w), wordData), w)
        val choices = Vector("bit-tree" -> bitForm, "word-mask" -> wordForm).map { case (form, expr) =>
          val plan = rewriter.plan(op, expr)
          reportCandidate(report, "composition:" + form, graph, op, None, pool, Some(expr), Some(plan), plan.reason)
          expr -> plan
        }
        val chosen = choices.filter(_._2.accepted).sortBy { case (_, p) =>
          (if (p.delta <= 0) 0 else 1, p.after, p.delta)
        }.headOption
        chosen.foreach { case (_, plan) => if (enabled) {
          rewriter.commit(plan); analysis.clear()
          stats = stats.copy(applied = stats.applied + 1, added = stats.added + plan.operations.size,
            removed = stats.removed + plan.removed.size)
        }}
      }
    }}
    stats
  }
}
