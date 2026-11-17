import essent.{TeAALDFGraphExtractor, TeAALTranspiler}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}
import scala.util.Random

object CheckNanhuOrderIndex {
  def main(args: Array[String]): Unit = {
    for (seed <- 0 until 6) {
      val random = new Random(seed)
      val ops = HashMap.empty[String, HashMap[String, HashSet[Int]]]
      val users = HashMap.empty[String, HashSet[String]]
      val producers = HashMap.empty[String, HashSet[String]]
      val outputs = HashMap.empty[String, String]
      val widths = HashMap.empty[String, Int]
      for (i <- 0 until 1400 + seed * 31) {
        val op = s"assign_+_$i"
        val input = if (i > 0 && random.nextInt(3) != 0)
          s"value${random.nextInt(i)}" else s"input${i % 1100}"
        val output = s"value$i"
        ops(op) = HashMap(input -> HashSet(0))
        users.getOrElseUpdate(input, HashSet.empty) += op
        producers(output) = HashSet(op)
        outputs(op) = output
        widths(op) = 64; widths(input) = 64; widths(output) = 64
      }
      val graph = new TeAALDFGraphExtractor(ops, users, producers, outputs, widths,
        HashSet.empty, HashSet.empty, ArrayBuffer.empty, HashSet.empty, HashMap.empty, HashMap.empty)
      Random.setSeed(seed)
      graph.DFGraphGen()
      sys.props.get("rteaal.exportCheckDir").foreach { directory =>
        val writer = new TeAALTranspiler(graph.opIndex)
        writer.extractDim(graph.nodeIDOrderMap)
        writer.tensorTocircInYML(graph.circuitInput, directory, s"input$seed")
        writer.tensorToInYML(graph.nodeIDOrderMap, graph.LAYER_NUM, graph.maxL,
          1, "I", "S", "O", directory, s"arguments$seed")
        writer.tensorToOpYML(graph.isnMap, graph.LAYER_NUM, graph.maxL,
          "I", "S", directory, s"operations$seed")
      }
      println(s"shape $seed ${graph.LAYER_NUM} ${graph.maxL}")
      println("input " + graph.circuitInput.mkString(","))
      println("pins " + graph.input_idx_map.toSeq.sortBy(_._1).map { case (pin, indices) =>
        pin + ":" + indices.mkString(",")
      }.mkString(";"))
      println("nodes " + graph.layerNodeIDN.toSeq.sortBy(_._1).map { case (layer, nodes) =>
        s"$layer:" + nodes.toSeq.sortBy(_._1).mkString(",")
      }.mkString(";"))
      println("tensor " + graph.nodeIDOrderMap.toSeq.sortBy(_._1).map { case (layer, nodes) =>
        s"$layer:" + nodes.toSeq.sortBy(_._1).map { case (node, inputs) =>
          s"$node:" + inputs.toSeq.sortBy(_._1).mkString(",")
        }.mkString(";")
      }.mkString("|"))
    }
  }
}
