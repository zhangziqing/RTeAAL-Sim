import essent.TeAALDFGraphConstProp
import scala.collection.mutable.{HashMap, HashSet}
import scala.util.Random

object CheckNanhuChainIndex {
  def main(args: Array[String]): Unit = {
    for (seed <- 0 until 120) {
      val random = new Random(seed)
      val ops = HashMap.empty[String, HashMap[String, HashSet[Int]]]
      val users = HashMap.empty[String, HashSet[String]]
      val producers = HashMap.empty[String, HashSet[String]]
      val outputs = HashMap.empty[String, String]
      val count = 350 + seed
      for (i <- 0 until count) {
        val kind = Seq("or", "xor", "add")(random.nextInt(3))
        val op = s"${kind}_+_$i"
        val inputs = HashMap.empty[String, HashSet[Int]]
        for (index <- 0 until 2) {
          val input = if (i > 0 && random.nextInt(5) != 0)
            s"value${random.nextInt(i)}" else s"input${random.nextInt(12)}"
          inputs.getOrElseUpdate(input, HashSet.empty) += index
          users.getOrElseUpdate(input, HashSet.empty) += op
        }
        ops(op) = inputs
        producers(s"value$i") = HashSet(op)
        outputs(op) = s"value$i"
      }
      TeAALDFGraphConstProp.update_op(count)
      val pass = new TeAALDFGraphConstProp(ops, users, producers, outputs, HashMap.empty)
      def canonical(groups: HashSet[HashSet[Int]]): String =
        groups.iterator.map(_.toSeq.sorted.mkString(",")).toSeq.sorted.mkString(";")
      println(s"$seed or ${canonical(pass.orChainExtract())}")
      println(s"$seed xor ${canonical(pass.xorChainExtract())}")
    }
  }
}
