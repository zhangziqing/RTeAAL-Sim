package essent

import essent.TeAALExtractor.{BufferHashMap, opInOrder}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Fuse scalar concat trees after constant/lookup optimization, before layering.
  * catn operands are [count, source0, offset0, ...], in high-to-low field order.
  * Offsets/count are constant slots until tensor preprocessing. All fields and
  * results have known positive widths, and every fused result fits in 64 bits.
  */
object FuseConcatOps {
  case class Stats(groups: Int = 0, removed: Int = 0, maxInputs: Int = 0)
  private case class Cat(left: String, right: String, shift: Int, out: String)

  def run(ops: opInOrder, users: BufferHashMap, producers: BufferHashMap,
          outputs: HashMap[String, String], widths: HashMap[String, Int],
          protectedOutputs: Set[String] = Set.empty): Stats = {
    if (sys.props.get("rteaal.fuseConcat").contains("false")) return Stats()
    val cats = HashMap.empty[String, Cat]
    ops.iterator.filter(_._1.startsWith("cat_+_")).foreach { case (op, inputs) =>
      val ordered = inputs.toSeq.flatMap { case (name, positions) => positions.map(_ -> name) }.toMap
      if (ordered.size == 3 && outputs.contains(op)) {
        val left = ordered(0)
        val right = ordered(1)
        val out = outputs(op)
        val lw = widths.getOrElse(left, 0)
        val rw = widths.getOrElse(right, 0)
        val ow = widths.getOrElse(out, 0)
        if (lw > 0 && rw > 0 && ow <= 64 && lw.toLong + rw == ow &&
            ordered(2).toIntOption.contains(rw)) cats(op) = Cat(left, right, rw, out)
      }
    }

    def child(signal: String): Option[String] = producers.get(signal).flatMap { ps =>
      if (ps.size == 1 && !protectedOutputs(signal) && users.get(signal).exists(_.size == 1))
        ps.headOption.filter(cats.contains)
      else None
    }
    // Process maximal trees once. A repeated operand is one consumer but remains
    // multiple ordered occurrences in the flattened operand list.
    val roots = cats.keysIterator.filter { op =>
      val out = cats(op).out
      protectedOutputs(out) || !users.get(out).exists(us => us.size == 1 && cats.contains(us.head))
    }.toVector.sorted
    var groups, removed, maxInputs = 0
    roots.foreach { root =>
      val leaves = ArrayBuffer.empty[(String, Int)]
      val absorbed = HashSet(root)
      val todo = ArrayBuffer((cats(root).right, 0), (cats(root).left, cats(root).shift))
      while (todo.nonEmpty) {
        val (signal, offset) = todo.remove(todo.size - 1)
        child(signal) match {
          case Some(op) =>
            val cat = cats(op)
            absorbed += op
            todo += ((cat.right, offset))
            todo += ((cat.left, offset + cat.shift))
          case None => leaves += ((signal, offset))
        }
      }
      if (absorbed.size > 1) {
        val out = cats(root).out
        val width = widths(out)
        absorbed.foreach { op =>
          ops(op).keysIterator.foreach { in =>
            users.get(in).foreach { us =>
              us -= op
              if (us.isEmpty) users.remove(in)
            }
          }
          producers.remove(outputs(op))
          outputs.remove(op)
          ops.remove(op)
          widths.remove(op)
        }
        val name = root.replace("cat_+_", "catn_+_")
        val inputs = HashMap.empty[String, HashSet[Int]]
        def add(signal: String, index: Int, constant: Boolean = false): Unit = {
          inputs.getOrElseUpdate(signal, HashSet.empty) += index
          users.getOrElseUpdate(signal, HashSet.empty) += name
          if (constant) widths.getOrElseUpdate(signal, 64)
        }
        add(leaves.size.toString, 0, true)
        leaves.zipWithIndex.foreach { case ((signal, offset), index) =>
          add(signal, 1 + 2 * index)
          add(offset.toString, 2 + 2 * index, true)
        }
        ops(name) = inputs
        outputs(name) = out
        producers(out) = HashSet(name)
        widths(name) = width
        groups += 1
        removed += absorbed.size - 1
        maxInputs = maxInputs.max(leaves.size)
      }
    }
    Stats(groups, removed, maxInputs)
  }
}
