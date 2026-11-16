package essent

import essent.SliceGraph._
import essent.ProjectSlices.Budget
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** One transaction owns both cost accounting and all tensor graph backfilling. */
object SliceRewrite {
  case class Operation(name: String, out: String, width: Int, inputs: Vector[String])
  case class Plan(root: String, operations: Vector[Operation], removed: Set[String],
                  before: Int, after: Int, shared: Vector[String], reason: String) {
    def delta: Int = operations.size - removed.size
    def accepted: Boolean = reason.isEmpty
  }
  class Rewriter(val graph: Graph, val pool: Pool, val budget: Budget) {
    private var serial = 0
    private var growth = 0
    private def fresh(kind: String): String = {
      var n = ""
      do { serial += 1; n = s"${kind}_+_projection_$serial" }
      while (graph.ops.contains(n) || graph.widths.contains("__" + n))
      n
    }
    def plan(root: String, expression: Int): Plan = {
      val out = graph.outputs(root)
      val before = graph.depth(out)
      val valueDepth = graph.expressionDepth(pool, expression)
      val rootValue = pool(expression)
      val needsAssign = rootValue.kind == "const" || graph.canReuseReference(rootValue)
      val after = valueDepth + (if (needsAssign) 1 else 0)
      def rejected(reason: String): Plan = Plan(root, Vector.empty, Set.empty, before, after, Vector.empty, reason)
      if (graph.protectedNames(root) || graph.aliases.getOrElse(root, HashSet.empty).size != 1)
        return rejected("protected-operation-or-output-alias")
      if (pool(expression).width != graph.width(out)) return rejected("output-width-mismatch")
      val refs = pool.references(expression)
      if (refs(out)) return rejected("unchanged-or-self-reference")
      val generated = ArrayBuffer.empty[Operation]
      val values = HashMap.empty[Int, String]
      pool.reachable(expression).foreach { id =>
        val e = pool(id)
        val isRoot = id == expression
        def emit(kind: String, inputs: Vector[String]): String = {
          val name = fresh(kind)
          val output = if (isRoot) out else "__" + name
          generated += Operation(name, output, e.width, inputs)
          output
        }
        values(id) = e.kind match {
          case "const" => e.value.toString
          case "ref" if graph.canReuseReference(e) => e.signal
          case "ref" if e.lo == 0 => emit("and", Vector(e.signal, mask(e.width).toString))
          case "ref" => emit("bits", Vector(e.signal, e.lo.toString, mask(e.width).toString))
          case "cat" => emit("cat", e.args.map(values) :+ pool(e.args(1)).width.toString)
          case "catn" =>
            // The expression DAG may concatenate many fields; tensor execution
            // retains the binary cat opcode and an ordered balanced tree.
            def tree(start: Int, end: Int): String = {
              if (end - start == 1) return values(e.args(start))
              val mid = start + (end - start) / 2
              val a = tree(start, mid); val b = tree(mid, end)
              val name = fresh("cat")
              val output = if (isRoot && start == 0 && end == e.args.size) out else "__" + name
              val width = e.args.slice(start, end).map(arg => pool(arg).width).sum
              val shift = e.args.slice(mid, end).map(arg => pool(arg).width).sum
              generated += Operation(name, output, width, Vector(a, b, shift.toString))
              output
            }
            tree(0, e.args.size)
          case other => emit(other, e.args.map(values))
        }
      }
      if (values(expression) != out) {
        val name = fresh("assign")
        generated += Operation(name, out, graph.width(out), Vector(values(expression)))
      }
      // Delete only producers made dead by this exact replacement. Protected
      // observations, retained shared users, and extra aliases keep their cones.
      val dead = HashSet(root)
      val work = ArrayBuffer.empty[String]
      work ++= graph.ops(root).keys
      while (work.nonEmpty) {
        val s = work.remove(work.size - 1)
        graph.producer(s).foreach { op =>
          val users = graph.liveUsers.getOrElse(s, HashSet.empty).toSet ++
            graph.users.getOrElse(s, HashSet.empty).filter(graph.ops.contains)
          if (!dead(op) && !refs(s) && graph.removable(op) && users.subsetOf(dead.toSet)) {
            dead += op
            work ++= graph.ops(op).keys
          }
        }
      }
      val shared = dead.iterator.flatMap(op => graph.ops(op).keys).filter(s =>
        graph.producer(s).exists(p => !dead(p))).toVector.distinct.sorted
      val delta = generated.size - dead.size
      val reason = if (generated.size > budget.maxAdded) "operator-budget"
        else if (delta > budget.maxGrowth || growth + delta.max(0) > budget.maxTotalGrowth) "growth-budget"
        else if (after > before || (delta > 0 && after >= before)) "no-depth-benefit"
        else ""
      Plan(root, generated.toVector, dead.toSet, before, after, shared, reason)
    }
    def commit(plan: Plan): Unit = {
      require(plan.accepted)
      val output = graph.outputs(plan.root)
      val changed = plan.removed.map(graph.outputs) ++ plan.operations.map(_.out)
      plan.removed.foreach { op =>
        graph.ops(op).keys.foreach { s =>
          graph.users.get(s).foreach { users =>
            users -= op
            if (users.isEmpty) graph.users.remove(s)
          }
          graph.liveUsers.get(s).foreach { users =>
            users -= op
            if (users.isEmpty) graph.liveUsers.remove(s)
          }
        }
        val out = graph.outputs(op)
        graph.producers.remove(out)
        graph.aliases.remove(op)
        graph.outputs.remove(op)
        graph.ops.remove(op)
        graph.widths.remove(op)
        if (out != output) graph.widths.remove(out)
      }
      plan.operations.foreach { n =>
        val ins = HashMap.empty[String, HashSet[Int]]
        n.inputs.zipWithIndex.foreach { case (s, i) =>
          ins.getOrElseUpdate(s, HashSet.empty) += i
          graph.users.getOrElseUpdate(s, HashSet.empty) += n.name
          if (number(s).isEmpty) graph.liveUsers.getOrElseUpdate(s, HashSet.empty) += n.name
          else graph.widths.getOrElseUpdate(s, 64)
        }
        graph.ops(n.name) = ins
        graph.outputs(n.name) = n.out
        graph.producers(n.out) = HashSet(n.name)
        graph.aliases(n.name) = HashSet(n.out)
        graph.widths(n.name) = n.width
        graph.widths(n.out) = n.width
      }
      growth += plan.delta.max(0)
      graph.invalidateDepths(changed + output)
    }
  }
}
