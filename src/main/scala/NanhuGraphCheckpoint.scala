package essent

import java.io.{BufferedInputStream, BufferedOutputStream, FileInputStream, FileOutputStream, ObjectInputStream, ObjectOutputStream}
import java.nio.file.{Files, Paths, StandardCopyOption}
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}
import essent.TeAALExtractor.{BufferHashMap, opInOrder}

@SerialVersionUID(1L)
case class NanhuGraphState(
  design: String, ops: opInOrder, users: BufferHashMap, producers: BufferHashMap,
  outputs: HashMap[String, String], widths: HashMap[String, Int],
  registers: HashSet[String], nextRegisters: HashSet[String],
  jumpTable: ArrayBuffer[String], shifts: HashSet[ArrayBuffer[String]],
  memoryInputs: HashMap[String, HashSet[Int]], randomInputs: HashMap[String, Int],
  inputRank: Int, operationCount: Int, uniqueOperations: Int
) extends Serializable

object NanhuGraphCheckpoint {
  def save(path: String, state: NanhuGraphState): Unit = {
    val temporary = Paths.get(path + ".tmp")
    val output = new ObjectOutputStream(new BufferedOutputStream(new FileOutputStream(temporary.toFile), 1 << 20))
    try output.writeObject(state) finally output.close()
    Files.move(temporary, Paths.get(path), StandardCopyOption.REPLACE_EXISTING, StandardCopyOption.ATOMIC_MOVE)
    println(s"[Nanhu] Saved optimized graph checkpoint $path")
  }

  def load(path: String): NanhuGraphState = {
    val input = new ObjectInputStream(new BufferedInputStream(new FileInputStream(path), 1 << 20))
    try input.readObject().asInstanceOf[NanhuGraphState] finally input.close()
  }

  def main(args: Array[String]): Unit = {
    require(args.length == 1, "Usage: essent.NanhuGraphCheckpoint SNAPSHOT")
    require(essent.passes.NanhuSimulation.enabled)
    val state = load(args(0))
    val design = sys.props.getOrElse("rteaal.design", state.design)
    require(design == state.design, "Checkpoint design differs from the requested design")
    val graph = new TeAALDFGraphExtractor(state.ops, state.users, state.producers,
      state.outputs, state.widths, state.registers, state.nextRegisters, state.jumpTable,
      state.shifts, state.memoryInputs, state.randomInputs)
    graph.DFGraphGen()
    val preserved = scala.io.Source.fromFile(sys.props("rteaal.preserved"))
    val missing = try preserved.getLines().map(_.trim).filter(_.nonEmpty)
      .filterNot(graph.dtmSignalCollect.contains).toVector finally preserved.close()
    require(missing.isEmpty, s"Observable pins lost during tensor optimization: ${missing.mkString(", ")}")
    val report = new TeAALReport(state.operationCount, state.uniqueOperations, graph.LAYER_NUM,
      graph.maxL, graph.TOTAL_IOP, state.users, state.producers, graph.inNeigh, graph.outNeigh)
    report.DFGraph_Report()
    val writer = new TeAALTranspiler(graph.opIndex)
    writer.dtmSignal(graph.dtmSignalCollect, "../../kernel/json", s"dtmSignal_$design")
    writer.InputRegMap(graph.input_idx_map, "../../kernel/json", s"InputRegMap_$design")
    writer.extractDim(graph.nodeIDOrderMap)
    writer.jumpTableGen(state.jumpTable, graph.layerNodeIDN, "../../kernel/txt", s"muxJT_$design")
    writer.tensorTocircInYML(graph.circuitInput, "../../kernel/txt", s"layerIn_$design")
    writer.tensorToInYML(graph.nodeIDOrderMap, graph.LAYER_NUM, graph.maxL, state.inputRank,
      "I", "S", "O", "../../kernel/yaml", s"operationInputMask_${design}_maskedIn_full_func")
    writer.tensorToOpYML(graph.isnMap, graph.LAYER_NUM, graph.maxL,
      "I", "S", "../../kernel/yaml", s"operationMask_${design}_maskedIn_full_func")
  }
}
