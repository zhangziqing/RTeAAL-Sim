package essent

import essent.TeAALExtractor.{BufferHashMap, opInOrder}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

/** Balance maximal bitwise AND/OR trees at the tensor-graph level.
  *
  * The pass starts from the real graph, so it can use actual arrival depths.
  * Single-use internal nodes are reassociated in place. A same-kind node on
  * the critical input that is shared by other consumers is cloned for this
  * tree (critical-path-aware duplication); the original stays intact for the
  * other consumers. A rewrite is accepted only when the root's arrival depth
  * strictly falls.
  */
object BalanceAndOrOps {
  case class Stats(groups: Int = 0, nodes: Int = 0, clones: Int = 0, maxInputs: Int = 0)
  private case class Tree(kind: String, left: String, right: String, out: String, width: Int)
  private case class Value(signal: String, width: Int, depth: Int)

  def run(ops: opInOrder, users: BufferHashMap, producers: BufferHashMap,
          outputs: HashMap[String, String], widths: HashMap[String, Int],
          protectedOutputs: Set[String] = Set.empty): Stats = {
    if (sys.props.get("rteaal.balanceAndOr").contains("false")) return Stats()
    val duplicate = !sys.props.get("rteaal.balanceAndOrDuplication").contains("false")
    val maxClones = sys.props.get("rteaal.balanceAndOrMaxClones").flatMap(_.toIntOption).getOrElse(8)

    def kindOf(name: String): String =
      if (name.startsWith("and_+_")) "and"
      else if (name.startsWith("or_+_")) "or"
      else ""

    def arguments(op: String): Map[Int, String] =
      ops(op).toSeq.flatMap { case (signal, ports) => ports.map(_ -> signal) }.toMap

    val trees = HashMap.empty[String, Tree]
    ops.foreach { case (op, inputs) =>
      val kind = kindOf(op)
      if (kind.nonEmpty && inputs.valuesIterator.flatten.toSet == Set(0, 1) && outputs.contains(op)) {
        val out = outputs(op)
        val width = widths.getOrElse(out, 0)
        val args = arguments(op)
        val left = args.getOrElse(0, "")
        val right = args.getOrElse(1, "")
        if (width > 0 && widths.getOrElse(left, 0) == width && widths.getOrElse(right, 0) == width &&
            producers.get(out).exists(_ == HashSet(op)) &&
            !protectedOutputs(op) && !protectedOutputs(out))
          trees(op) = Tree(kind, left, right, out, width)
      }
    }
    if (trees.isEmpty) return Stats()

    val depths = HashMap.empty[String, Int]
    def signalDepth(signal: String): Int = depths.getOrElseUpdate(signal, {
      producers.get(signal) match {
        case Some(ps) if ps.nonEmpty =>
          1 + ps.iterator.flatMap(op => ops.get(op).toSeq.flatMap(_.keys)).map(signalDepth).maxOption.getOrElse(0)
        case _ => 0
      }
    })

    def freshOp(kind: String): String = {
      var index = 0
      var name = s"${kind}_+_dup${index}"
      while (ops.contains(name)) { index += 1; name = s"${kind}_+_dup${index}" }
      name
    }
    def freshSignal(base: String): String = {
      var index = 0
      var name = s"${base}__rteaal_andor_dup_${index}"
      while (producers.contains(name) || widths.contains(name) || users.contains(name)) {
        index += 1; name = s"${base}__rteaal_andor_dup_${index}"
      }
      name
    }

    var groups, nodes, cloneCount, maxInputs = 0
    // Mark signals consumed by any tree; a tree whose output is consumed by
    // another tree is an internal node, not a root. This must stay linear.
    val consumed = HashSet.empty[String]
    trees.valuesIterator.foreach { tree =>
      consumed += tree.left
      consumed += tree.right
    }
    val roots = trees.keysIterator.filter(op => !consumed(trees(op).out)).toVector
    val rootDepths = roots.map(op => op -> signalDepth(trees(op).out))
    val maxDepth = rootDepths.map(_._2).maxOption.getOrElse(0)
    val window = sys.props.get("rteaal.balanceAndOrDepthWindow").flatMap(_.toIntOption).getOrElse(8)
    val targets = rootDepths.filter(_._2 >= maxDepth - window).sortBy(x => (-x._2, x._1)).map(_._1)

    targets.foreach { rootOp =>
      val root = trees(rootOp)
      val leaves = ArrayBuffer.empty[Value]
      val absorbed = HashSet(rootOp)
      val cloned = ArrayBuffer.empty[String]
      val createdOps = ArrayBuffer.empty[String]
      val createdSignals = ArrayBuffer.empty[String]
      var budget = maxClones

      def cloneTree(op: String): String = {
        val tree = trees(op)
        val newOp = freshOp(tree.kind)
        val newOut = freshSignal(tree.out)
        val inputs = HashMap.empty[String, HashSet[Int]]
        ops(op).foreach { case (signal, ports) =>
          inputs(signal) = ports.clone()
          users.getOrElseUpdate(signal, HashSet.empty) += newOp
        }
        ops(newOp) = inputs
        outputs(newOp) = newOut
        widths(newOp) = tree.width
        widths(newOut) = tree.width
        producers(newOut) = HashSet(newOp)
        trees(newOp) = Tree(tree.kind, tree.left, tree.right, newOut, tree.width)
        createdOps += newOp
        createdSignals += newOut
        cloned += newOp
        budget -= 1
        newOp
      }

      def child(signal: String, consumer: String, critical: Boolean): Option[String] = {
        if (budget < 0) return None
        producers.get(signal).flatMap { ps =>
          if (ps.size != 1) None
          else {
            val op = ps.head
            trees.get(op) match {
              case Some(tree) if tree.kind == root.kind && tree.width == root.width &&
                  !protectedOutputs(op) && !protectedOutputs(signal) =>
                if (users.get(signal).exists(_ == HashSet(consumer)) &&
                    ops(consumer).get(signal).exists(_.size == 1)) Some(op)
                else if (duplicate && critical && budget > 0) Some(cloneTree(op))
                else None
              case _ => None
            }
          }
        }
      }

      def visit(op: String, critical: Boolean): Unit = {
        val tree = trees(op)
        val dl = signalDepth(tree.left)
        val dr = signalDepth(tree.right)
        val leftCritical = dl >= dr
        def process(signal: String, childCritical: Boolean): Unit = {
          child(signal, op, childCritical) match {
            case Some(next) =>
              absorbed += next
              visit(next, childCritical)
            case None =>
              leaves += Value(signal, widths.getOrElse(signal, 0), signalDepth(signal))
          }
        }
        process(tree.left, critical && leftCritical)
        process(tree.right, critical && !leftCritical)
      }
      visit(rootOp, critical = true)

      val before = signalDepth(root.out)
      val valid = absorbed.size > 1 && leaves.size == absorbed.size + 1 &&
        leaves.forall(_.width == root.width)
      if (!valid) {
        // Roll back clones; no original graph state was rewritten.
        createdOps.foreach { op =>
          ops(op).keysIterator.foreach { signal =>
            users.get(signal).foreach { us => us -= op; if (us.isEmpty) users.remove(signal) }
          }
          ops.remove(op); outputs.remove(op); widths.remove(op); trees.remove(op)
        }
        createdSignals.foreach { signal => producers.remove(signal); widths.remove(signal) }
      } else {
        val available = absorbed.toVector.filterNot(_ == rootOp).sorted.iterator
        val planned = ArrayBuffer.empty[(String, Value, Value, Value)]
        def tree(start: Int, end: Int, top: Boolean = false): Value = {
          if (end - start == 1) return leaves(start)
          val mid = start + (end - start) / 2
          val a = tree(start, mid)
          val b = tree(mid, end)
          val op = if (top) rootOp else available.next()
          val out = Value(outputs(op), root.width, a.depth.max(b.depth) + 1)
          planned += ((op, a, b, out))
          out
        }
        val result = tree(0, leaves.size, top = true)
        if (result.depth >= before) {
          createdOps.foreach { op =>
            ops(op).keysIterator.foreach { signal =>
              users.get(signal).foreach { us => us -= op; if (us.isEmpty) users.remove(signal) }
            }
            ops.remove(op); outputs.remove(op); widths.remove(op); trees.remove(op)
          }
          createdSignals.foreach { signal => producers.remove(signal); widths.remove(signal) }
        } else {
          absorbed.foreach { op =>
            ops(op).keysIterator.foreach { signal =>
              users.get(signal).foreach { us => us -= op; if (us.isEmpty) users.remove(signal) }
            }
          }
          planned.foreach { case (op, a, b, out) =>
            val inputs = HashMap.empty[String, HashSet[Int]]
            Seq(a.signal, b.signal).zipWithIndex.foreach { case (signal, index) =>
              inputs.getOrElseUpdate(signal, HashSet.empty) += index
              users.getOrElseUpdate(signal, HashSet.empty) += op
            }
            ops(op) = inputs
            widths(out.signal) = root.width
            depths(out.signal) = out.depth
          }
          groups += 1
          nodes += absorbed.size
          cloneCount += cloned.size
          maxInputs = maxInputs.max(leaves.size)
        }
      }
    }
    Stats(groups, nodes, cloneCount, maxInputs)
  }
}
