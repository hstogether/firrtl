 
package midas

import Utils._
import firrtl._
import firrtl.Utils._

/** FAME-1 Transformation
 *
 * This pass takes a lowered-to-ground circuit and performs a FAME-1 (Decoupled) transformation 
 *   to the circuit
 * It does this by creating a simulation module wrapper around the circuit, if we can gate the 
 *   clock, then there need be no modification to the target RTL, if we can't, then the target
 *   RTL will have to be modified (by adding a midasFire input and use this signal to gate 
 *   register enable
 *
 * ALGORITHM
 *  1. Flatten RTL 
 *     a. Create NewTop
 *     b. Instantiate Top in NewTop
 *     c. Iteratively pull all sim tagged instances out of hierarchy to NewTop
 *        i. Move instance declaration from child module to parent module
 *        ii. Create io in child module corresponding to io of instance
 *        iii. Connect original instance io in child to new child io
 *        iv. Connect child io in parent to instance io
 *        v. Repeate until instance is in SimTop 
 *           (if black box, repeat until completely removed from design)
 *     * Post-flattening invariants
 *       - No combinational logic on NewTop
 *       - All and only instances in NewTop are sim tagged
 *       - No black boxes in design
 *  2. Simulation Transformation
 *     a. Iteratively transform each inst in Top (see example firrtl in dram_midas top dir)
 *        i.   Create wrapper class
 *        ii.  Create input and output (ready, valid) pairs for every other sim module this module connects to
 *             * Note that TopIO counts as a "sim module"
 *        iii. Create simFire as AND of inputs.valid and outputs.ready
 *        iv.  Create [target] simClock as AND of simFire and [host] clock
 *        v.   Connect target IO to wrapper IO, except connect target clock to simClock
 *
 * TODO 
 *  - Implement Flatten RTL
 *  - Check that circuit is in LowFIRRTL?
 *
 * NOTES 
 *   - How do we only transform the necessary modules? Should there be a MIDAS list of modules 
 *     or something?
 *     * YES, this will be done by requiring the user to instantiate modules that should be split
 *       with something like: val module = new MIDASModule(class... etc.)
 *   - There cannot be nested DecoupledIO or ValidIO
 *   - How do output consumes tie in to MIDAS fire? If all of our outputs are not consumed
 *     in a given cycle, do we block midas$fire on the next cycle? Perhaps there should be 
 *     a register for not having consumed all outputs last cycle
 *   - If our outputs are not consumed we also need to be sure not to consume out inputs,
 *     so the logic for this must depend on the previous cycle being consumed as well
 *   - We also need a way to determine the difference between the MIDAS modules and their
 *     connecting Queues, perhaps they should be MIDAS queues, which then perhaps prints
 *     out a listing of all queues so that they can be properly transformed
 *       * What do these MIDAS queues look like since we're enforcing true decoupled 
 *         interfaces?
 */
object Fame1 {

  private def getDefInsts(s: Stmt): Seq[DefInst] = {
    s match {
      case i: DefInst => Seq(i)
      case b: Block => b.stmts.map(getDefInsts).flatten
      case _ => Seq()
    }
  }
  private def getDefInsts(m: Module): Seq[DefInst] = getDefInsts(m.stmt)

  private def getDefInstRef(inst: DefInst): Ref = {
    inst.module match {
      case ref: Ref => ref
      case _ => throw new Exception("Invalid module expression for DefInst: " + inst.serialize)
    }
  }

  // DefInsts have an Expression for the module, this expression should be a reference this 
  //   reference has a tpe that should be a bundle representing the IO of that module class
  private def getDefInstType(inst: DefInst): BundleType = {
    val ref = getDefInstRef(inst)
    ref.tpe match {
      case b: BundleType => b
      case _ => throw new Exception("Invalid reference type for DefInst: " + inst.serialize)
    }
  }

  private def getModuleFromDefInst(nameToModule: Map[String, Module], inst: DefInst): Module = {
    val instModule = getDefInstRef(inst)
    if(!nameToModule.contains(instModule.name))
      throw new Exception(s"Module ${instModule.name} not found in circuit!")
    else 
      nameToModule(instModule.name)
  }

  // ***** findPortConn *****
  // This takes lowFIRRTL top module that follows invariants described above and returns a connection Map
  //   of instanceName -> (instanctPorts -> portEndpoint)
  // It honestly feels kind of brittle given it assumes there will be no intermediate nodes or anything in 
  //  the way of direct connections between IO of module instances
  private type PortMap = Map[String, String]
  private val  PortMap = Map[String, String]()
  private type ConnMap = Map[String, PortMap]
  private val  ConnMap = Map[String, PortMap]()
  private def processConnectExp(exp: Exp): (String, String) = {
    val unsupportedExp = new Exception("Unsupported Exp for finding port connections: " + exp)
    exp match {
      case ref: Ref => ("topIO", ref.name)
      case sub: Subfield => 
        sub.exp match {
          case ref: Ref => (ref.name, sub.name)
          case _ => throw unsupportedExp
        }
      case exp: Exp => throw unsupportedExp
    }
  }
  private def processConnect(conn: Connect): ConnMap = {
    val lhs = processConnectExp(conn.lhs)
    val rhs = processConnectExp(conn.rhs)
    Map(lhs._1 -> Map(lhs._2 -> rhs._1), rhs._1 -> Map(rhs._2 -> lhs._1)).withDefaultValue(PortMap)
  }
  private def findPortConn(connMap: ConnMap, stmts: Seq[Stmt]): ConnMap = {
    if (stmts.isEmpty) connMap
    else {
      stmts.head match {
        case conn: Connect => {
          val newConnMap = processConnect(conn)
          findPortConn(connMap map {case (k,v) => k -> (v ++ newConnMap(k)) }, stmts.tail)
        }
        case _ => findPortConn(connMap, stmts.tail)
      }
    }
  }
  private def findPortConn(top: Module, insts: Seq[DefInst]): ConnMap = {
    val initConnMap = (insts map ( _.name -> PortMap )).toMap ++ Map("topIO" -> PortMap)
    val topStmts = top.stmt match {
      case b: Block => b.stmts
      case s: Stmt => Seq(s) // This honestly shouldn't happen but let's be safe
    }
    findPortConn(initConnMap, topStmts)
  }

  private def wrapName(name: String): String = "SimWrap_" + name
  private def unwrapName(name: String): String = name.stripPrefix("SimWrap_")

  // ***** genWrapperModule *****
  // Generates FAME-1 Decoupled wrappers for simulation module instances
  private val hostReady = Field("hostReady", Reverse, UIntType(IntWidth(1)))
  private val hostValid = Field("hostValid", Default, UIntType(IntWidth(1)))
  private val hostClock = Port(NoInfo, "hostClock", Input, ClockType)

  private def genWrapperModule(inst: DefInst, portMap: PortMap): Module = {
    println(s"Wrapping ${inst.name}")
    println(portMap)
    val instIO = getDefInstType(inst)
    val nameToField = (instIO.fields map (f => f.name -> f)).toMap

    val connections = (portMap map(_._2)).toSeq.distinct // modules this inst connects to
    // Build simPort for each connecting module
    // TODO This whole chunk really ought to be rewritten or made a function
    val connPorts = connections map { c =>
      // Get ports that connect to this particular module as fields
      val fields = (portMap filter (_._2 == c)).keySet.toSeq.sorted map (nameToField(_))
      val noClock = fields filter (_.tpe != ClockType) // Remove clock
      val inputSet  = noClock filter (_.dir == Reverse) map (f => Field(f.name, Default, f.tpe))
      val outputSet = noClock filter (_.dir == Default)
      Port(inst.info, c, Output, BundleType(
        (if (inputSet.isEmpty) Seq()
        else
          Seq(Field("hostIn",  Reverse, BundleType(Seq(hostReady, hostValid) :+
                                          Field("hostBits", Default, BundleType(inputSet)))))
        ) ++
        (if (outputSet.isEmpty) Seq()
        else
          Seq(Field("hostOut", Default, BundleType(Seq(hostReady, hostValid) :+
                                          Field("hostBits", Default, BundleType(outputSet)))))
        )
      ))
    }
    val ports = hostClock +: connPorts // Add host Clock

    // targetFire is signal to indicate when a simulation module can execute, this is indicated by all of its inputs
    //   being valid and all of its outputs being ready
    val targetFireInputs = (connPorts map { port => 
      getFields(port) map { field => 
        field.dir match {
          case Reverse => buildExp(Seq(port.name, field.name, hostValid.name)) 
          case Default => buildExp(Seq(port.name, field.name, hostReady.name))
        }
      }
    }).flatten

    val targetFire = DefNode(inst.info, "targetFire", genPrimopReduce(And, targetFireInputs))
    // targetClock is the simple AND of targetFire and the hostClock so that the rtl module only executes when data 
    //   is available and outputs are ready
    val targetClock = DefNode(inst.info, "targetClock", DoPrimop(And, 
                     Seq(buildExp(targetFire.name), buildExp(hostClock.name)), Seq(), UnknownType))

    // As a simple RTL module, we're always ready
    val inputsReady = (connPorts map { port => 
      getFields(port) filter (_.dir == Reverse) map { field => // filter to only take inputs
        Connect(inst.info, buildExp(Seq(port.name, field.name, hostReady.name)), UIntValue(1, IntWidth(1)))
      }
    }).flatten

    // Outputs are valid on cycles where we fire
    val outputsValid = (connPorts map { port => 
      getFields(port) filter (_.dir == Default) map { field => // filter to only take outputs
        Connect(inst.info, buildExp(Seq(port.name, field.name, hostValid.name)), buildExp(targetFire.name))
      }
    }).flatten

    // Connect up all of the IO of the RTL module to sim module IO, except clock which should be connected
    // This currently assumes naming things that are also done above when generating connPorts
    val connectedInstIOFields = instIO.fields filter(field => portMap.contains(field.name)) // skip unconnected IO
    val instIOConnect = connectedInstIOFields map { field =>
      field.tpe match {             
        case ClockType => Connect(inst.info, Ref(field.name, field.tpe), Ref(targetClock.name, ClockType))
        case _ => field.dir match {
          case Default => Connect(inst.info, buildExp(Seq(portMap(field.name), "hostOut", field.name)), 
                                             buildExp(Seq(inst.name, field.name)))
          case Reverse => Connect(inst.info, buildExp(Seq(inst.name, field.name)),
                                             buildExp(Seq(portMap(field.name), "hostIn", field.name)))
        }
      }
    }
    //val stmts = Block(Seq(simFire, simClock, inst) ++ inputsReady ++ outputsValid ++ instIOConnect)
    val stmts = Block(Seq(targetFire, targetClock) ++ inputsReady ++ outputsValid ++ Seq(inst) ++ instIOConnect)

    Module(inst.info, wrapName(inst.name), ports, stmts)
  }



  // ***** generateSimQueues *****
  // Takes Seq of SimWrapper modules
  // Returns Map of (src, dest) -> SimQueue
  def generateSimQueues(wrappers: Seq[Module]): Map[(String, String), Module] = {
    def rec(wrappers: Seq[Module], map: Map[(String, String), Module]): Map[(String, String), Module] = {
      if (wrappers.isEmpty) map
      else {
        val w = wrappers.head
        val name = unwrapName(w.name)
        val newMap = w.ports filter(isSimPort) map { port =>
          splitSimPort(port) map { field =>
            val (src, dst) = if (field.dir == Default) (name, port.name) else (port.name, name)
            if (map.contains((src, dst))) Map[(String, String), Module]()
            else (src, dst) -> buildSimQueue(s"SimQueue_${src}_${dst}", getHostBits(field).tpe)
          }
        }
        println(newMap)
        rec(wrappers.tail, map ++ Map())
      }
    }
    rec(wrappers, Map[(String, String), Module]())
  }

  // ***** transform *****
  // Perform FAME-1 Transformation for MIDAS
  def transform(c: Circuit): Circuit = {
    // We should check that the invariants mentioned above are true
    val nameToModule = (c.modules map (m => m.name -> m))(collection.breakOut): Map[String, Module] 
    val top = nameToModule(c.name)

    val insts = getDefInsts(top)

    val portConn = findPortConn(top, insts)
    // Check that port Connections include all ports for each instance?

    val wrappers = insts map (inst => genWrapperModule(inst, portConn(inst.name)))

    generateSimQueues(wrappers)
    //val w = wrappers.head
    //println(w.serialize)
    //w.ports filter (isSimPort) map { p => 
    //  splitSimPort(p) foreach { f => 
    //    val queueName = if (f.dir == Default) s"${w.name}_${p.name}" else s"${p.name}_${w.name}"
    //    println(buildSimQueue("SimQueue_" + queueName, getHostBits(f).tpe))
    //  }
    //  //println(buildSimQueue(,p.tpe)) 
    //}

    c
  }

}