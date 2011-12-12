package silAST.methods.implementations

import scala.collection.{Seq, Set}
import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.source.SourceLocation

final class BasicBlock private[silAST](
                                        sl: SourceLocation,
                                        val label: String,
                                        private[implementations] val cfg: ControlFlowGraph
                                        ) extends ASTNode(sl) {
  private[implementations] def addPredecessor(edge: CFGEdge) {
    require(edge.target == this)
    pPredecessors += edge
  }

  private[implementations] def addSuccessor(edge: CFGEdge) {
    require(edge.source == this)
    pSuccessors += edge
  }

  override def toString =
    "\t" + label + ":{\n" +
      (if (!statements.isEmpty) statements.mkString("\t\t", "\n\t\t", "\n") else "") +
      (if (!successors.isEmpty) ("\t\tgoto " + (for (s <- successors) yield s.target.label).mkString(",") + "\n") else "") +
      "\t}\n"

  private val pStatements = new ListBuffer[Statement]
  private val pSuccessors = new ListBuffer[CFGEdge]
  private val pPredecessors = new ListBuffer[CFGEdge]

  private[silAST] def appendStatement(s: Statement) = {
    require(!(pStatements contains s))
    pStatements += s
  }

  def statements: Seq[Statement] = pStatements.result()

  def successors: Set[CFGEdge] = pSuccessors.result().toSet

  def predecessors: Set[CFGEdge] = pPredecessors.result().toSet

  cfg.addNode(this)
}
