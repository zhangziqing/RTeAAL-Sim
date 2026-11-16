import essent.TeAALDFGraphConstProp
import scala.collection.mutable.{HashMap, HashSet}

/** Small regression: a three-mux lookup output feeds both XOR and another mux. */
object CheckSharedMuxRoot {
  def main(args: Array[String]): Unit = {
    val inputs = HashMap.empty[String, HashMap[String, HashSet[Int]]]
    val consumers = HashMap.empty[String, HashSet[String]]
    val producers = HashMap.empty[String, HashSet[String]]
    val outputs = HashMap.empty[String, String]
    val widths = HashMap("selector" -> 2)
    def add(op: String, out: String, args: String*): Unit = {
      val ordered = HashMap.empty[String, HashSet[Int]]
      args.zipWithIndex.foreach { case (arg, index) =>
        ordered.getOrElseUpdate(arg, HashSet.empty) += index
        consumers.getOrElseUpdate(arg, HashSet.empty) += op
      }
      inputs(op) = ordered
      producers(out) = HashSet(op)
      outputs(op) = out
      widths(out) = 1
      widths(op) = 1
    }
    for (i <- 1 to 3) {
      add(s"eq_+_${2 * i}", s"cond$i", "selector", s"UInt<2>(\"h$i\")")
      add(s"mux_+_${2 * i + 1}", s"q$i", s"cond$i", s"r$i", if (i == 1) "r0" else s"q${i - 1}")
    }
    add("xor_+_8", "xorOut", "q3", "flag")
    add("mux_+_9", "muxOut", "enable", "other", "q3")
    val te = new TeAALDFGraphConstProp(inputs, consumers, producers, outputs, widths)
    te.op_counter = 10
    val roots = te.findMuxChainRoot()
    require(roots.contains("mux_+_7"), "The shared lookup output must be a root")
    val cases = te.classAdjust(te.chainClassification(te.chainTraceBack(roots)))(1)
    require(cases("mux_+_7").size == 3)
    require(te.caseChainChecker("mux_+_7", cases("mux_+_7")))
    val (records, conditions) = te.muxRecordReform(cases)
    val tables = te.newMuxChainInfoExtract(cases, records, conditions)
    require(tables.size == 1 && tables.values.head.toSeq == Seq("r0", "r1", "r2", "r3"))
    te.new_updateMuxChain(tables, records, conditions)
    require(outputs("chain_+_10") == "q3")
    require(consumers("q3").toSet == Set("xor_+_8", "mux_+_9"))
    require((1 to 3).forall(i => !inputs.contains(s"mux_+_${2 * i + 1}")))
    require((0 to 3).forall(i => consumers(s"r$i").contains("chain_+_10")))
    println("PASS shared three-mux root: four selectors, default, consumers and lookup dependencies")
  }
}
