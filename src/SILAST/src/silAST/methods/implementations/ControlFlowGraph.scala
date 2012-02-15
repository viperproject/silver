package silAST.methods.implementations

import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.source.{noLocation, SourceLocation}

final class ControlFlowGraph private[silAST](
                                              val sourceLocation : SourceLocation,
                                              private val implementationFactory : ImplementationFactory
                                              ) extends ASTNode {
  def compile()
  {
    require(pStartNode!=None)
    require(pEndNode!=None)

  }

  //TODO: more consistency checks
  require(implementationFactory!=null)

  private val pNodes = new ListBuffer[BasicBlock]
  def nodes : Set[BasicBlock] = pNodes.toSet

  private var pStartNode :Option[BasicBlock] = None
  private var pEndNode  :Option[BasicBlock] = None

  private[implementations] def addNode(bb: BasicBlock) = {
    require(!(pNodes contains bb))
    require(bb.cfg == this)
    pNodes += bb
  }

  private[implementations] def setStartNode(bb: BasicBlock)
  {
    require(pNodes contains bb)
    pStartNode = Some(bb)
  }

  private[implementations] def setEndNode(bb: BasicBlock)
  {
    require(pNodes contains bb)
    pEndNode = Some(bb)
  }

  def startNode: BasicBlock = pStartNode match { case Some(n) => n case None => throw new Exception() }

  def endNode: BasicBlock = pEndNode match { case Some(n) => n  case None => throw new Exception() }

  override def toString = pNodes.mkString("\n")

  override def equals(other : Any) : Boolean = {
    other match{
      case c : ControlFlowGraph => c eq this
      case _ => false
    }
  }
  override def hashCode() : Int = nodes.hashCode()
}