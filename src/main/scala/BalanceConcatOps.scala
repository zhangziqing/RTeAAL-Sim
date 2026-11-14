package essent

import essent.TeAALExtractor.{BufferHashMap, opInOrder}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Reassociate scalar concatenations using only the existing binary cat opcode.
  * Field order is immutable. Shared, aliased and observable intermediates are
  * boundaries; every accepted replacement reduces its actual arrival depth.
  */
object BalanceConcatOps {
  case class Stats(groups: Int = 0, nodes: Int = 0, maxInputs: Int = 0)
  private case class Cat(left: String, right: String, shift: Int, out: String)
  private case class Value(signal: String, width: Int, depth: Int)

  def run(ops: opInOrder, users: BufferHashMap, producers: BufferHashMap,
          outputs: HashMap[String, String], widths: HashMap[String, Int],
          protectedOutputs: Set[String] = Set.empty): Stats = {
    if (sys.props.get("rteaal.balanceConcat").contains("false")) return Stats()
    val cats = HashMap.empty[String, Cat]
    ops.iterator.filter(_._1.startsWith("cat_+_")).foreach { case (op, inputs) =>
      val ordered = inputs.toSeq.flatMap { case (s, ps) => ps.map(_ -> s) }.toMap
      if (ordered.keySet == Set(0, 1, 2) && outputs.contains(op) && !protectedOutputs(op)) {
        val left = ordered(0)
        val right = ordered(1)
        val out = outputs(op)
        val lw = widths.getOrElse(left, 0)
        val rw = widths.getOrElse(right, 0)
        val ow = widths.getOrElse(out, 0)
        if (lw > 0 && rw > 0 && ow <= 64 && lw.toLong + rw == ow &&
            producers.get(out).exists(_ == HashSet(op)) && ordered(2).toIntOption.contains(rw))
          cats(op) = Cat(left, right, rw, out)
      }
    }
    val aliased = HashSet.empty[String]
    producers.foreach { case (signal, ps) => ps.foreach { op =>
      cats.get(op).foreach(cat => if (cat.out != signal) aliased += op)
    }}
    cats --= aliased
    if (cats.isEmpty) return Stats()
    val candidateSignals = cats.valuesIterator.map(_.out).toSet
    val liveUsers = HashMap.empty[String, HashSet[String]]
    ops.foreach { case (op, inputs) => inputs.keysIterator.filter(candidateSignals).foreach { signal =>
      liveUsers.getOrElseUpdate(signal, HashSet.empty) += op
    }}
    def child(signal: String, consumer: String): Option[String] = producers.get(signal).flatMap { ps =>
      if (ps.size == 1 && !protectedOutputs(signal) &&
          users.get(signal).exists(_ == HashSet(consumer)) &&
          liveUsers.get(signal).exists(_ == HashSet(consumer)) &&
          ops(consumer).get(signal).exists(_.size == 1))
        ps.headOption.filter(op => cats.get(op).exists(_.out == signal))
      else None
    }
    val roots = cats.keysIterator.filter { op =>
      val out = cats(op).out
      !liveUsers.get(out).exists(us => us.size == 1 && cats.contains(us.head) &&
        child(out, us.head).contains(op))
    }.toVector

    // Sort disjoint trees in dependency order. Clear the original-depth cache
    // before rewriting: later trees then see the updated depths of earlier ones.
    // No previously cached ancestor can depend on a tree still to be processed.
    val depths = HashMap.empty[String, Int]
    def dependencies(signal: String): Vector[String] = producers.get(signal).toVector
      .flatMap(_.iterator).filter(ops.contains).flatMap(op => ops(op).keysIterator).distinct
    def arrival(signal: String): Int = {
      val pending = ArrayBuffer(signal -> false)
      val visiting = HashSet.empty[String]
      while (pending.nonEmpty) {
        val (s, ready) = pending.remove(pending.size - 1)
        if (!depths.contains(s)) {
          val ds = dependencies(s)
          if (ds.isEmpty) depths(s) = 0
          else if (ready) {
            depths(s) = 1 + ds.iterator.map(depths).max
            visiting -= s
          } else {
            require(visiting.add(s), s"Combinational cycle at $s")
            pending += s -> true
            ds.foreach(d => pending += d -> false)
          }
        }
      }
      depths(signal)
    }
    val orderedRoots = roots.map(op => (op, arrival(cats(op).out))).sortBy(x => (x._2, x._1))
    depths.clear()
    var groups, nodes, maxInputs = 0
    orderedRoots.foreach { case (root, _) =>
      val leaves = ArrayBuffer.empty[Value]
      val absorbed = HashSet(root)
      val todo = ArrayBuffer(cats(root).right -> root, cats(root).left -> root)
      while (todo.nonEmpty) {
        val (signal, consumer) = todo.remove(todo.size - 1)
        child(signal, consumer) match {
          case Some(op) =>
            absorbed += op
            todo += cats(op).right -> op
            todo += cats(op).left -> op
          case None => leaves += Value(signal, widths(signal), arrival(signal))
        }
      }
      if (absorbed.size > 1) {
        require(leaves.size == absorbed.size + 1, "Concat intermediates must have one occurrence")
        val before = arrival(cats(root).out)
        val available = absorbed.toVector.filterNot(_ == root).sorted.iterator
        val planned = ArrayBuffer.empty[(String, Value, Value, Value)]
        def tree(start: Int, end: Int, top: Boolean = false): Value = {
          if (end - start == 1) return leaves(start)
          val mid = start + (end - start) / 2
          val a = tree(start, mid)
          val b = tree(mid, end)
          val op = if (top) root else available.next()
          val out = Value(outputs(op), a.width + b.width, a.depth.max(b.depth) + 1)
          planned += ((op, a, b, out))
          out
        }
        val result = tree(0, leaves.size, top = true)
        if (result.depth < before) {
          absorbed.foreach { op => ops(op).keysIterator.foreach { in =>
            users.get(in).foreach { us =>
              us -= op
              if (us.isEmpty) users.remove(in)
            }
          }}
          planned.foreach { case (op, a, b, out) =>
            val inputs = HashMap.empty[String, HashSet[Int]]
            Seq(a.signal, b.signal, b.width.toString).zipWithIndex.foreach { case (s, i) =>
              inputs.getOrElseUpdate(s, HashSet.empty) += i
              users.getOrElseUpdate(s, HashSet.empty) += op
            }
            widths.getOrElseUpdate(b.width.toString, 64)
            ops(op) = inputs
            widths(op) = out.width
            widths(out.signal) = out.width
            depths(out.signal) = out.depth
          }
          groups += 1
          nodes += absorbed.size
          maxInputs = maxInputs.max(leaves.size)
        }
      }
    }
    Stats(groups, nodes, maxInputs)
  }
}
