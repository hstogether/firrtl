// See LICENSE for license details.

package firrtl
package transforms

import firrtl.ir._
import firrtl.Utils._
import firrtl.Mappers._
import firrtl.WrappedExpression._
import firrtl.graph.DiGraph

import scala.collection.mutable

/** Replace wires with nodes in a legal, flow-forward order
  *
  *  This pass must run after LowerTypes because Aggregate-type
  *  wires have multiple connections that may be impossible to order in a
  *  flow-foward way
  */
class RemoveWires extends Transform {
  def inputForm = LowForm
  def outputForm = LowForm

  // Extract all referential expressions from a possibly nested expression
  // This is similar to the function in DeadCodeElimination but also accepts WSubIndex
  // TODO could this be generalized by supporting WSubAccess and thus not doing error checking?
  private def extractRefs(expr: Expression): Seq[Expression] = {
    val refs = mutable.ArrayBuffer.empty[Expression]
    def rec(e: Expression): Expression = {
      e match {
        case expr @ (_: WRef | _: WSubField | _: WSubIndex) => refs += expr
        case nested @ (_: Mux | _: DoPrim | _: ValidIf) => nested map rec
        case ignore @ (_: Literal) => // Do nothing
        case unexpected => throwInternalError
      }
      e
    }
    rec(expr)
    refs
  }

  // Transform netlist into DefNodes
  private def getOrderedNodes(
      netlist: mutable.LinkedHashMap[WrappedExpression, (Expression, Info)]): Seq[DefNode] = {
    val edges = netlist.map { case (sink, (expr, _)) => sink -> extractRefs(expr).map(we(_)).toSet }
    val edgeGraph = DiGraph(edges.toMap)

    val ordered = edgeGraph.linearize.reverse
    ordered.map { key =>
      val WRef(name, _,_,_) = key.e1
      val (rhs, info) = netlist(key)
      DefNode(info, name, rhs)
    }
  }

  private def onModule(m: DefModule): DefModule = {
    // Store all non-node declarations here (like reg, inst, and mem)
    val decls = mutable.ArrayBuffer.empty[Statement]
    // Store all "other" statements here, non-wire, non-node connections, printfs, etc.
    val otherStmts = mutable.ArrayBuffer.empty[Statement]
    // Add nodes and wire connection here
    val netlist = mutable.LinkedHashMap.empty[WrappedExpression, (Expression, Info)]
    // Info at definition of wires for combining into node
    val wireInfo = mutable.HashMap.empty[WrappedExpression, Info]

    def onStmt(stmt: Statement): Statement = {
      stmt match {
        case DefNode(info, name, expr) =>
          netlist(we(WRef(name))) = (expr, info)
        case wire: DefWire if !wire.tpe.isInstanceOf[AnalogType] => // Remove all non-Analog wires
          wireInfo(WRef(wire)) = wire.info
        case decl: IsDeclaration => // Keep all declarations except for nodes and non-Analog wires
          decls += decl
        case con @ Connect(cinfo, lhs, rhs) => kind(lhs) match {
          case WireKind =>
            // Be sure to pad the rhs since nodes get their type from the rhs
            val paddedRhs = ConstantPropagation.pad(rhs, lhs.tpe)
            val dinfo = wireInfo(lhs)
            netlist(we(lhs)) = (paddedRhs, MultiInfo(Seq(dinfo, cinfo)))
          case _ => otherStmts += con // Other connections just pass through
        }
        case invalid @ IsInvalid(info, expr) =>
          kind(expr) match {
            case WireKind =>
              val width = expr.tpe match { case GroundType(width) => width } // LowFirrtl
              netlist(we(expr)) = (ValidIf(Utils.zero, UIntLiteral(BigInt(0), width), expr.tpe), info)
            case _ => otherStmts += invalid
          }
        case other @ (_: Print | _: Stop | _: Attach) =>
          otherStmts += other
        case EmptyStmt => // Dont bother keeping EmptyStmts around
        case block: Block => block map onStmt
        case _ => throwInternalError
      }
      stmt
    }

    m match {
      case Module(info, name, ports, body) =>
        onStmt(body)
        val logic = getOrderedNodes(netlist)
        Module(info, name, ports, Block(decls ++ logic ++ otherStmts))
      case m: ExtModule => m
    }
  }

  def execute(state: CircuitState): CircuitState = {
    val newCircuit = state.circuit map onModule
    state.copy(circuit = newCircuit)
  }
}