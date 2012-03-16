package silAST.methods.implementations

import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.source.SourceLocation
import silAST.methods.Scope

final class ControlFlowGraph private[silAST]
  (
    val sourceLocation: SourceLocation,
    val scope : Scope,
    val implementation : Implementation
  )
  extends ASTNode
{
  def compile() {
    require(pStartNode != None)
    require(pEndNode != None)
    require(nodes.forall(_.pControlStatement!=None))
  }

  //TODO: more consistency checks
  require(scope != null)
  def nodes: Set[Block] = pNodes.toSet

  private[implementations] def addNode(b: Block) = {
    require(!(pNodes contains b))
    require(b.cfg eq this)
    pNodes += b
  }
  private[implementations] def setStartNode(b : BasicBlock) {
    require(pNodes contains b)
    pStartNode = Some(b)
  }

  private[implementations] def setEndNode(b: BasicBlock) {
    require(pNodes contains b)
    pEndNode = Some(b)
  }

  def startNode: BasicBlock = pStartNode match {
    case Some(n) => n
    case None => throw new Exception()
  }

  def endNode: BasicBlock = pEndNode match {
    case Some(n) => n
    case None => throw new Exception()
  }

  private val pNodes = new ListBuffer[Block]
  private[silAST] var pStartNode: Option[BasicBlock] = None
  private[silAST] var pEndNode: Option[BasicBlock] = None

  /////////////////////////////////////////////////////////////////
  override def toString = pNodes.mkString("\n")

  override def equals(other: Any): Boolean = {
    other match {
      case c: ControlFlowGraph => c eq this
      case _ => false
    }
  }

  override def hashCode(): Int = nodes.hashCode()
}