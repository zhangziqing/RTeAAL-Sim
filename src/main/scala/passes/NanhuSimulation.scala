package essent.passes

import firrtl._
import firrtl.ir._
import firrtl.Mappers._
import firrtl.PrimOps._
import essent.Extract._

/** Experimental, opt-in models for the pinned Nanhu simulation harness.
  * CPU/cache RTL is unchanged. RAM is bounded to 256 MiB; the runner must reject
  * accesses outside that range. Flash matches difftest's default boot image.
  * JTAG is idle and SD access is rejected by the runner.
  */
object NanhuSimulation {
  val enabled: Boolean = sys.props.get("rteaal.nanhu").contains("true")
  val ramWords: Long = 1L << 25
  private def isHelper(name: String): Boolean =
    name.matches("(RAMHelper|FlashHelper|SDHelper)(_[0-9]+)?")

  private def lower(text: String): Module = {
    val c = Parser.parse(text.linesIterator)
    val state = new firrtl.stage.transforms.Compiler(firrtl.stage.Forms.LowFormOptimized)
      .execute(CircuitState(c, Seq()))
    state.circuit.modules.collectFirst { case m: Module if m.name == c.main => m }.get
  }

  def replace(c: Circuit): Circuit = c.copy(modules = c.modules.map {
    case e: ExtModule if e.defname == "RAMHelper" => lower(s"""circuit ${e.name} :
  module ${e.name} :
    input clk : Clock
    input en : UInt<1>
    input rIdx : UInt<64>
    output rdata : UInt<64>
    input wIdx : UInt<64>
    input wdata : UInt<64>
    input wmask : UInt<64>
    input wen : UInt<1>
    mem mem :
      data-type => UInt<64>
      depth => $ramWords
      reader => r
      reader => old
      writer => w
      read-latency => 0
      write-latency => 1
      read-under-write => undefined
    mem.r.clk <= clk
    mem.r.en <= en
    mem.r.addr <= bits(rIdx, 24, 0)
    mem.old.clk <= clk
    mem.old.en <= UInt<1>(1)
    mem.old.addr <= bits(wIdx, 24, 0)
    mem.w.clk <= clk
    mem.w.en <= and(en, wen)
    mem.w.mask <= UInt<1>(1)
    mem.w.addr <= bits(wIdx, 24, 0)
    mem.w.data <= or(and(wdata, wmask), and(mem.old.data, not(wmask)))
    rdata <= mux(en, mem.r.data, UInt<64>(0))
""")
    case e: ExtModule if e.defname == "FlashHelper" => lower(s"""circuit ${e.name} :
  module ${e.name} :
    input clk : Clock
    input ren : UInt<1>
    output data : UInt<64>
    input addr : UInt<32>
    reg value : UInt<64>, clk
    node index = bits(addr, 31, 3)
    node word = mux(eq(index, UInt<29>(0)), UInt<64>("h01f292930010029b"), mux(eq(index, UInt<29>(1)), UInt<64>("h0000000000028067"), UInt<64>(0)))
    value <= mux(ren, word, value)
    data <= value
""")
    case e: ExtModule if e.defname == "SimJTAG" =>
      val outputs = e.ports.filter(_.direction == Output)
      require(outputs.forall(p => p.tpe == ClockType || p.tpe.isInstanceOf[UIntType]),
        "Unexpected SimJTAG output type")
      val assigns = outputs.map { p =>
        val value = if (p.name == "jtag_TMS") 1 else 0
        val width = p.tpe match { case UIntType(w: IntWidth) => w; case ClockType => IntWidth(1) }
        val literal = UIntLiteral(value, width)
        val expr = if (p.tpe == ClockType) DoPrim(AsClock, Seq(literal), Nil, ClockType) else literal
        Connect(NoInfo, WRef(p.name, p.tpe, PortKind, SinkFlow), expr)
      }
      Module(e.info, e.name, e.ports, Block(assigns))
    case e: ExtModule if e.defname == "SDHelper" =>
      Module(e.info, e.name, e.ports, Connect(NoInfo,
        WRef("data", UIntType(IntWidth(32)), PortKind, SinkFlow), UIntLiteral(0, IntWidth(32))))
    case e: ExtModule if e.defname == "TLLogWriter" =>
      require(e.ports.forall(_.direction == Input), "TLLogWriter must be an observation-only sink")
      e
    case e: ExtModule =>
      require(e.defname.startsWith("Difftest") || e.defname == "STD_CLKGT_func",
        s"Unmodeled Nanhu external module: ${e.name} (${e.defname})")
      e
    case m => m
  })

  // Keep the DPI event sinks and harness bounds checks visible in the tensor.
  def writePreserved(c: Circuit): Unit = {
    val interfaces = findAllModuleInstances(c).flatMap { case (name, prefix) =>
      findModule(name, c) match {
        case e: ExtModule => Some(ujson.Obj("module" -> e.defname, "prefix" -> prefix,
          "inputs" -> ujson.Arr.from(e.ports.filter(p => p.direction == Input && p.tpe != ClockType).map(_.name)),
          "outputs" -> ujson.Arr.from(e.ports.filter(p => p.direction == Output && p.tpe != ClockType).map(_.name))))
        case m: Module if isHelper(m.name) =>
          Some(ujson.Obj("module" -> m.name, "prefix" -> prefix,
            "inputs" -> ujson.Arr.from(m.ports.filter(p => p.direction == Input && p.tpe != ClockType).map(_.name))))
        case _ => None
      }
    }
    val selected = findAllModuleInstances(c).flatMap { case (name, prefix) =>
      findModule(name, c) match {
        case e: ExtModule if e.defname.startsWith("Difftest") =>
          e.ports.filter(p => p.direction == Input && p.tpe != ClockType).map(p => prefix + p.name)
        case m: Module if isHelper(m.name) =>
          m.ports.filter(p => p.direction == Input && p.tpe != ClockType && !p.name.startsWith("__rteaal_ce_")).map(p => prefix + p.name)
        case m: Module if m.name == c.main =>
          m.ports.filter(p => p.direction == Output && p.tpe != ClockType).map(p => prefix + p.name)
        case _ => Nil
      }
    }.distinct.sorted
    val file = sys.props.getOrElse("rteaal.preserved", "preserved_signals.txt")
    val writer = new java.io.PrintWriter(file)
    try selected.foreach(writer.println) finally writer.close()
    val manifest = new java.io.PrintWriter(file + ".interfaces.json")
    try manifest.write(ujson.Arr.from(interfaces).render(indent = 2)) finally manifest.close()
    println(s"[Nanhu] Preserved ${selected.size} event/harness signals in $file")
  }
}

/** Lower clock events to data enables before the upstream pass erases clocks.
  * Supports clock wires, hierarchy, constant idle clocks, register-generated
  * clocks and Nanhu's STD_CLKGT_func. Unknown clock sources fail explicitly.
  * This is edge based: a clock gate uses E sampled before the main rising edge.
  */
object NanhuClockEnables {
  private val bit = UIntType(IntWidth(1))
  private val one = UIntLiteral(1, IntWidth(1))
  private val zero = UIntLiteral(0, IntWidth(1))
  private def ceName(name: String): String = "__rteaal_ce_" + name
  private def and(a: Expression, b: Expression): Expression = (a, b) match {
    case (`one`, x) => x
    case (x, `one`) => x
    case (`zero`, _) | (_, `zero`) => zero
    case _ => DoPrim(And, Seq(a, b), Nil, bit)
  }

  def run(c: Circuit): Circuit = {
    val moduleMap = c.modules.map(m => m.name -> m).toMap
    val parents = c.modules.collect { case m: Module =>
      findInstancesOf[WDefInstance](m.body).map(i => i.module -> (m.name, i.name))
    }.flatten.groupBy(_._1).map { case (name, entries) => name -> entries.map(_._2) }
    // Only prove an inverted clock idle when every instance traces back to a
    // constant source. An inverted master clock must still fail explicitly.
    val clockDefinitions = scala.collection.mutable.Map.empty[String, Map[String, Expression]]
    def clockDefs(name: String): Map[String, Expression] = clockDefinitions.getOrElseUpdate(name, {
      val defs = scala.collection.mutable.Map.empty[String, Expression]
      moduleMap(name) match {
        case m: Module =>
          def gather(s: Statement): Unit = { s match {
            case d: DefNode if d.value.tpe == ClockType || d.value.tpe == bit => defs(d.name) = d.value
            case a: Connect if a.expr.tpe == ClockType || a.expr.tpe == bit => defs(a.loc.serialize) = a.expr
            case _ =>
          }; s.foreachStmt(gather) }
          gather(m.body)
        case _ =>
      }
      defs.toMap
    })
    val idleCache = scala.collection.mutable.Map.empty[(String, String), Boolean]
    def isIdle(name: String, e: Expression, seen: Set[(String, String)] = Set.empty): Boolean = {
      val key = name -> e.serialize
      if (seen(key)) false else idleCache.getOrElseUpdate(key, {
        val next = seen + key
        e match {
          case _: UIntLiteral | _: SIntLiteral => true
          case r: WRef if r.kind == RegKind => false
          case r: WRef if moduleMap(name).ports.exists(p => p.name == r.name && p.direction == Input) =>
            val callers = parents.getOrElse(name, Nil)
            name != c.main && callers.nonEmpty && callers.forall { case (parent, inst) =>
              clockDefs(parent).get(s"$inst.${r.name}").exists(x => isIdle(parent, x, next))
            }
          case WSubField(WRef(inst, _, _, _), port, _, _) =>
            val child = moduleMap(name) match {
              case m: Module => findInstancesOf[WDefInstance](m.body).find(_.name == inst).map(_.module)
              case _ => None
            }
            child.exists(n => clockDefs(n).get(port).exists(x => isIdle(n, x, next)))
          case p: DoPrim => p.args.forall(x => isIdle(name, x, next))
          case _ => clockDefs(name).get(e.serialize).exists(x => isIdle(name, x, next))
        }
      })
    }
    val inputCarriers = scala.collection.mutable.Map.empty[String, Set[String]]
    // AsClock(AsUInt(clock)) occurs at XSTop's Bool clock interface.
    c.modules.foreach {
      case m: Module =>
        val defs = scala.collection.mutable.Map.empty[String, Expression]
        def gather(s: Statement): Unit = { s match {
          case d: DefNode => defs(d.name) = d.value
          case a: Connect => defs(a.loc.serialize) = a.expr
          case _ =>
        }; s.foreachStmt(gather) }
        gather(m.body)
        val carrier = scala.collection.mutable.Set.empty[String]
        def roots(e: Expression, seen: Set[String] = Set.empty): Unit = e match {
          case r: WRef if !seen(r.name) =>
            if (m.ports.exists(p => p.name == r.name && p.direction == Input)) carrier += r.name
            else defs.get(r.name).foreach(x => roots(x, seen + r.name))
          case p: DoPrim if p.op == AsUInt || p.op == AsClock => p.args.foreach(x => roots(x, seen))
          case _ =>
        }
        def scanE(e: Expression): Unit = { e match {
          case p: DoPrim if p.op == AsClock => roots(p.args.head)
          case _ =>
        }; e.foreachExpr(scanE) }
        def scan(s: Statement): Unit = { s.foreachExpr(scanE); s.foreachStmt(scan) }
        scan(m.body)
        inputCarriers(m.name) = carrier.toSet ++ m.ports.filter(p => p.direction == Input && p.tpe == ClockType).map(_.name)
      case _ =>
    }
    // A Bool clock can be forwarded through several modules before AsClock.
    // Propagate carrier requirements back through child input connections.
    var changed = true
    while (changed) {
      changed = false
      c.modules.foreach {
        case m: Module =>
          val defs = scala.collection.mutable.Map.empty[String, Expression]
          val instances = findInstancesOf[WDefInstance](m.body).map(i => i.name -> i.module).toMap
          def gather(s: Statement): Unit = { s match {
            case n: DefNode => defs(n.name) = n.value
            case a: Connect => defs(a.loc.serialize) = a.expr
            case _ =>
          }; s.foreachStmt(gather) }
          gather(m.body)
          val required = scala.collection.mutable.Set.empty[String] ++ inputCarriers(m.name)
          def roots(e: Expression, seen: Set[String] = Set.empty): Unit = e match {
            case r: WRef if !seen(r.name) =>
              if (m.ports.exists(p => p.name == r.name && p.direction == Input)) required += r.name
              else defs.get(r.name).foreach(x => roots(x, seen + r.name))
            case p: DoPrim if p.op == AsUInt || p.op == AsClock => p.args.foreach(x => roots(x, seen))
            case _ =>
          }
          def scan(s: Statement): Unit = { s match {
            case Connect(_, WSubField(WRef(inst, _, _, _), port, _, _), rhs)
                if instances.contains(inst) && inputCarriers.getOrElse(instances(inst), Set.empty)(port) => roots(rhs)
            case _ =>
          }; s.foreachStmt(scan) }
          scan(m.body)
          if (required.toSet != inputCarriers(m.name)) {
            inputCarriers(m.name) = required.toSet
            changed = true
          }
        case _ =>
      }
    }
    var guardedRegisters = 0
    var guardedWrites = 0
    val modules = c.modules.map {
      case m: Module =>
        val definitions = scala.collection.mutable.Map.empty[String, Expression]
        val registers = findInstancesOf[DefRegister](m.body).map(r => r.name -> r).toMap
        val instances = findInstancesOf[WDefInstance](m.body).map(i => i.name -> i.module).toMap
        def gather(s: Statement): Unit = { s match {
          case n: DefNode => definitions(n.name) = n.value
          case a: Connect => definitions(a.loc.serialize) = a.expr
          case _ =>
        }; s.foreachStmt(gather) }
        gather(m.body)
        val carriers = inputCarriers(m.name)
        def enable(e: Expression, seen: Set[String] = Set.empty): Expression = {
          val key = e.serialize
          require(!seen(key), s"Clock alias cycle in ${m.name}: $key")
          val nextSeen = seen + key
          e match {
            case _: UIntLiteral => zero // a constant clock has no rising edges
            case p: DoPrim if p.op == AsClock || p.op == AsUInt => enable(p.args.head, nextSeen)
            case p: DoPrim if isIdle(m.name, p) => zero
            case r: WRef if carriers(r.name) =>
              if (m.name == c.main) {
                require(r.tpe == ClockType && r.name == "clock", s"Unknown top clock ${r.name}")
                one
              } else WRef(ceName(r.name), bit, PortKind, SourceFlow)
            case r: WRef if registers.contains(r.name) =>
              val reg = registers(r.name)
              val oldLow = DoPrim(Not, Seq(r), Nil, bit)
              and(enable(reg.clock, nextSeen), and(oldLow, definitions(r.name)))
            case f @ WSubField(WRef(inst, _, _, _), port, _, _) if instances.contains(inst) =>
              moduleMap(instances(inst)) match {
                case ext: ExtModule if ext.defname == "STD_CLKGT_func" && port == "Q" =>
                  def pin(name: String) = definitions(s"$inst.$name")
                  and(enable(pin("CK"), nextSeen), DoPrim(Or, Seq(pin("E"), pin("TE")), Nil, bit))
                case child: Module if child.ports.exists(p => p.name == port && p.direction == Output && p.tpe == ClockType) =>
                  WSubField(f.expr, ceName(port), bit, SourceFlow)
                case _ if definitions.contains(key) => enable(definitions(key), nextSeen)
                case _ => throw new IllegalArgumentException(s"Unsupported clock $key in ${m.name}")
              }
            case _ if definitions.contains(key) => enable(definitions(key), nextSeen)
            case _ => throw new IllegalArgumentException(s"Unsupported clock $key in ${m.name}")
          }
        }
        def rewrite(s: Statement): Statement = s match {
          case b: Block => b.copy(stmts = b.stmts.map(rewrite))
          case a: Connect if Utils.kind(a.loc) == RegKind =>
            val reg = registers(a.loc.serialize)
            val en = enable(reg.clock)
            if (en == one) a else {
              guardedRegisters += 1
              a.copy(expr = Mux(en, a.expr, WRef(reg.name, reg.tpe, RegKind, SourceFlow), reg.tpe))
            }
          case a @ Connect(_, WSubField(WSubField(WRef(mem, _, MemKind, _), port, _, _), "en", _, _), _) =>
            val en = enable(definitions(s"$mem.$port.clk"))
            if (en == one) a else { guardedWrites += 1; a.copy(expr = and(en, a.expr)) }
          case a @ Connect(_, loc @ WSubField(WRef(inst, _, _, _), port, _, _), rhs)
              if instances.contains(inst) && inputCarriers.getOrElse(instances(inst), Set.empty)(port) =>
            val dst = WSubField(loc.expr, ceName(port), bit, SinkFlow)
            Block(Seq(a, Connect(NoInfo, dst, enable(rhs))))
          case a => a
        }
        val extraPorts = if (m.name == c.main) Nil else
          m.ports.collect {
            case p if carriers(p.name) => Port(NoInfo, ceName(p.name), Input, bit)
            case p if p.direction == Output && p.tpe == ClockType => Port(NoInfo, ceName(p.name), Output, bit)
          }
        val outputs = m.ports.filter(p => p.direction == Output && p.tpe == ClockType).map { p =>
          Connect(NoInfo, WRef(ceName(p.name), bit, PortKind, SinkFlow), enable(definitions(p.name)))
        }
        m.copy(ports = m.ports ++ extraPorts, body = Block(Seq(rewrite(m.body)) ++ outputs))
      case e => e
    }
    println(s"[Nanhu] Clock enables: $guardedRegisters register updates, $guardedWrites memory enables")
    c.copy(modules = modules)
  }
}

// RTeAAL's expression extractor expects named operands for compound muxes.
// Clock enables introduce additional mux nesting after FIRRTL's normal splits.
object NanhuSimpleExpressions {
  def run(c: Circuit): Circuit = c.copy(modules = c.modules.map {
    case m: Module =>
      val namespace = Namespace(m)
      def normalize(e: Expression): Expression = e match {
        case p: DoPrim if p.op == Head || p.op == Tail =>
          val width = p.args.head.tpe.asInstanceOf[GroundType].width.asInstanceOf[IntWidth].width
          val count = p.consts.head
          val (high, low) = if (p.op == Head) (width - 1, width - count)
            else (width - count - 1, BigInt(0))
          require(high >= low && low >= 0, s"Invalid Nanhu slice: ${p.serialize}")
          DoPrim(Bits, p.args, Seq(high, low), p.tpe)
        case x => x
      }
      def stmt(s: Statement): Statement = s match {
        case b: Block => b.copy(stmts = b.stmts.map(stmt))
        case _ =>
          val nodes = scala.collection.mutable.ArrayBuffer.empty[Statement]
          def atom(e: Expression): Expression = {
            val mapped = normalize(e.map(atom))
            mapped match {
              case _: DoPrim | _: Mux | _: ValidIf =>
                val name = namespace.newName("__rteaal_expr")
                nodes += DefNode(NoInfo, name, mapped)
                WRef(name, mapped.tpe, NodeKind, SourceFlow)
              case x => x
            }
          }
          val result = s.mapExpr(e => normalize(e.map(atom)))
          if (nodes.isEmpty) result else Block(nodes.toSeq :+ result)
      }
      m.copy(body = stmt(m.body))
    case x => x
  })
}
