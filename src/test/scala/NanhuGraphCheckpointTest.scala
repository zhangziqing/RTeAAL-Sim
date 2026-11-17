package essent

import java.nio.file.Files
import org.scalatest.flatspec.AnyFlatSpec
import scala.collection.mutable.{ArrayBuffer, HashMap, HashSet}

class NanhuGraphCheckpointTest extends AnyFlatSpec {
  "An optimized graph checkpoint" should "retain all graph and export metadata after the compiler clears its buffers" in {
    val directory = Files.createTempDirectory("nanhu-graph-checkpoint-")
    val path = directory.resolve("graph.bin")
    val state = NanhuGraphState("checkpoint-control",
      HashMap("xor_+_1" -> HashMap("state" -> HashSet(0), "input" -> HashSet(1, 2))),
      HashMap("state" -> HashSet("xor_+_1"), "input" -> HashSet("xor_+_1")),
      HashMap("state@next" -> HashSet("xor_+_1")),
      HashMap("xor_+_1" -> "state@next"),
      HashMap("state" -> 65, "state@next" -> 65, "input" -> 65, "xor_+_1" -> 65),
      HashSet("state"), HashSet("state@next"), ArrayBuffer("lookup-output"),
      HashSet(ArrayBuffer("shr_+_2", "shr_+_3")),
      HashMap("memw_+_4" -> HashSet(2, 3)), HashMap("random-input" -> 17),
      inputRank = 3, operationCount = 5, uniqueOperations = 1)
    try {
      NanhuGraphCheckpoint.save(path.toString, state)
      val loaded = NanhuGraphCheckpoint.load(path.toString)
      assert(loaded == state)
      state.ops.clear()
      state.users.clear()
      state.producers.clear()
      assert(loaded.ops("xor_+_1")("input") == HashSet(1, 2))
      assert(NanhuGraphCheckpoint.load(path.toString) == loaded)
      assert(!Files.exists(directory.resolve("graph.bin.tmp")))
      NanhuGraphCheckpoint.save(path.toString, loaded.copy(design = "replacement"))
      assert(NanhuGraphCheckpoint.load(path.toString).design == "replacement")
      assert(!Files.exists(directory.resolve("graph.bin.tmp")))
    } finally {
      Files.deleteIfExists(path)
      Files.deleteIfExists(directory)
    }
  }
}
