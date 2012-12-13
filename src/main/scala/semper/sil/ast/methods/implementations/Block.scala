package semper.sil.ast.methods.implementations

import semper.sil.ast.ASTNode
import collection.mutable.ListBuffer
import scala.Predef._
import semper.sil.ast.programs.symbols.ProgramVariable

trait Block
  extends ASTNode {
  def controlStatement: ControlStatement = pControlStatement match {
    case Some(cs) => cs
    case _ => throw new Exception()
  }

  def implementation: Implementation

  def label: String

  def successors: Set[CFGEdge] = controlStatement.successors

  def predecessors: Set[CFGEdge] = pPredecessors.result().toSet

  def factory: BlockFactory

  def cfg: ControlFlowGraph //where am I

  def readVariables: Set[ProgramVariable]

  def writtenVariables: Set[ProgramVariable]


  private[implementations] def addPredecessor(edge: CFGEdge) {
    require(edge.target == this)
    pPredecessors += edge
  }

  private[implementations] def setControlStatement(cs: ControlStatement) {
    require(cs.successors.forall(_.source == this))
    require(pControlStatement == None)
    pControlStatement = Some(cs)
  }

  private val pPredecessors = new ListBuffer[CFGEdge]
  private [sil] var pControlStatement: Option[ControlStatement] = None

  protected def controlFlowToString = (if (!successors.isEmpty) ("\t\tgoto " + (for (s <- successors) yield {
    s.condition.toString + " ⇒ " + s.target.label
  }).mkString(",") + "\n")
  else "")
}
