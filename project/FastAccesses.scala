import sbt._
import sbt.Keys._
import scala.sys.process._

object FastAccesses {
  val checkFastAccesses = taskKey[Unit]("Compare stock, optimized and cached RemoveAccesses lowering")

  def build(id: String, scalaRelease: String, firrtlRelease: String): Project = {
    val binary = CrossVersion.binaryScalaVersion(scalaRelease)
    Project(id, file("tools/firrtl-fast-accesses") / id).settings(
      scalaVersion := scalaRelease,
      libraryDependencies := Seq("edu.berkeley.cs" %% "firrtl" % firrtlRelease),
      Compile / scalaSource := baseDirectory.value.getParentFile / "src",
      Compile / resourceDirectory := baseDirectory.value.getParentFile / "resources",
      Compile / packageBin / artifactPath :=
        (LocalRootProject / baseDirectory).value / "utils/bin" / s"firrtl-fast-accesses-$binary.jar",
      publish / skip := true,
      checkFastAccesses := {
        val optimized = (Compile / packageBin).value
        val dependencies = (Runtime / externalDependencyClasspath).value.files
        val stock = dependencies.find(_.getName.startsWith("firrtl_")).get
        val fixture = baseDirectory.value.getParentFile / "test/NestedAccess.fir"
        val work = java.nio.file.Files.createTempDirectory(target.value.toPath, "check-").toFile
        val javaBin = file(sys.props("java.home")) / "bin/java"
        val outputs = Seq("stock", "fast", "cached").map { mode =>
          val classpath = (if (mode == "stock") dependencies else optimized +: dependencies).mkString(java.io.File.pathSeparator)
          val output = work / s"$mode.lo.fir"
          val log = work / s"$mode.log"
          val command = Seq(javaBin.toString, "-XX:ActiveProcessorCount=4", "-Xmx4g",
            "-Xlog:class+load=info", s"-Dfirrtl.fastAccesses.useCache=${mode == "cached"}",
            "-cp", classpath, "firrtl.stage.FirrtlMain", "-i", fixture.toString,
            "-o", output.toString, "-X", "low")
          require((Process(command, work) #> log).! == 0, s"$mode lowering failed; see $log")
          val origin = if (mode == "stock") stock else optimized
          require(IO.readLines(log).exists(line => line.contains("firrtl.passes.RemoveAccesses$ source:") &&
            line.contains(origin.getName)), s"Unexpected RemoveAccesses class origin; see $log")
          IO.readBytes(output)
        }
        require(outputs.tail.forall(_.sameElements(outputs.head)), s"Low FIRRTL differs; see $work")
        streams.value.log.info(s"PASS Scala $binary / FIRRTL $firrtlRelease: stock/fast/cached byte-identical; class origins checked ($work)")
      }
    )
  }
}
