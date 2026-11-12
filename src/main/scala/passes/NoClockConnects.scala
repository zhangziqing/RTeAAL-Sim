package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.options.Dependency
import firrtl.passes._
import firrtl.Utils._


object NoClockConnects extends Pass {
  def desc = "Removes Connects or DefNodes to anything that is ClockType"
  // FUTURE: remove this pass and properly support multi-clock

  override def prerequisites = Seq(Dependency(essent.passes.ReplaceAsyncRegs))
  override def optionalPrerequisites = firrtl.stage.Forms.LowFormOptimized
  override def invalidates(a: Transform) = false

  def cutConnectsStmt(s: Statement): Statement = {
    def lowClockLevels(e: Expression): Expression = e.map(lowClockLevels) match {
      // The scheduler evaluates the combinational circuit before a master edge.
      // Nanhu exposes that master clock as Bool at its SoC boundary.
      case p: DoPrim if NanhuSimulation.enabled && p.op == firrtl.PrimOps.AsUInt &&
          p.args.head.tpe == ClockType => UIntLiteral(0, IntWidth(1))
      case e => e
    }
    val noConnects = s match {
      case c: Connect if (c.expr.tpe == ClockType || c.loc.tpe == ClockType) => EmptyStmt
      case d: DefNode if (d.value.tpe == ClockType) => EmptyStmt
      case _ => if (NanhuSimulation.enabled) s.mapExpr(lowClockLevels) else s
    }
    noConnects map cutConnectsStmt
  }

  def noConnectsModule(m: Module): Module = {
    Module(m.info, m.name, m.ports, squashEmpty(cutConnectsStmt(m.body)))
  }

  def run(c: Circuit): Circuit = {
    if (NanhuSimulation.enabled) sys.props.get("rteaal.preClockDump").foreach { path =>
      val writer = new java.io.PrintWriter(path)
      try writer.write(c.serialize) finally writer.close()
      println(s"[Nanhu] Wrote pre-clock Low FIRRTL checkpoint to $path")
    }
    val input = if (NanhuSimulation.enabled)
      NanhuClockEnables.run(NanhuSimulation.replace(c)) else c
    val modulesx = input.modules.map {
      case m: ExtModule => m
      case m: Module => noConnectsModule(m)
    }
    Circuit(c.info, modulesx, c.main)
  }
}
