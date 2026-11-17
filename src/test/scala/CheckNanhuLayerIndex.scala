import essent.{TeAALDFGraphExtractor, TeAALExtractor}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}
import scala.util.Random

object CheckNanhuLayerIndex {
  def main(args: Array[String]): Unit = {
    for (seed <- 0 until 40) {
      val random = new Random(seed)
      val groups = HashSet.empty[ArrayBuffer[String]]
      for (_ <- 0 until 80)
        groups += ArrayBuffer.fill(2 + random.nextInt(6))(s"shift${random.nextInt(200)}")
      val graph = new TeAALDFGraphExtractor(HashMap.empty, HashMap.empty, HashMap.empty,
        HashMap.empty, HashMap.empty, HashSet.empty, HashSet.empty, ArrayBuffer.empty,
        groups, HashMap.empty, HashMap.empty)
      for (i <- 0 until 240) {
        val op = s"shift$i"
        println(s"shift $seed $op ${graph.dshiftCheck(op)} ${graph.dshiftExtract(op).mkString(",")}")
      }
    }
    for (seed <- 0 until 80) {
      val random = new Random(seed)
      val predecessors = HashMap.empty[String, HashSet[String]]
      val successors = HashMap.empty[String, HashSet[String]]
      val inputs = HashMap.empty[String, HashSet[String]]
      val count = 240 + seed
      for (i <- 0 until count) {
        val node = s"node$i"
        val previous = HashSet.empty[String]
        for (_ <- 0 until random.nextInt(5)) {
          if (i > 0) previous += s"node${random.nextInt(i)}"
        }
        if (previous.nonEmpty) {
          predecessors(node) = previous
          previous.foreach { p => successors.getOrElseUpdate(p, HashSet.empty) += node }
        } else inputs.getOrElseUpdate("input", HashSet.empty) += node
      }
      // Exercise the upstream full-scan fallback as well as ordinary edges.
      successors.keys.toSeq.sorted.zipWithIndex.foreach { case (node, i) =>
        if (i % 7 == 0) successors.remove(node)
      }
      val graph = new TeAALDFGraphExtractor(HashMap.empty, HashMap.empty, HashMap.empty,
        HashMap.empty, HashMap.empty, HashSet.empty, HashSet.empty, ArrayBuffer.empty,
        HashSet.empty, HashMap.empty, HashMap.empty)
      graph.layerExtract(successors, predecessors, inputs, HashMap.empty)
      require(predecessors.isEmpty)
      println(s"$seed " + graph.layerMap.toSeq.sortBy(_._1).map { case (layer, nodes) =>
        layer + ":" + nodes.toSeq.sorted.mkString(",")
      }.mkString(";"))
    }
  }
}
