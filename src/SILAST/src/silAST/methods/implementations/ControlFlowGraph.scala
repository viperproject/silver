package silAST.methods.implementations

import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.source.{noLocation, SourceLocation}

final class ControlFlowGraph private[silAST](
                                              sl: SourceLocation,
                                              private val implementationFactory : ImplementationFactory
                                              ) extends ASTNode(sl) {
  def compile()
  {
    require(pStartNode!=None)
    require(pEndNode!=None)

  }

  //TODO: more consistency checks
  require(implementationFactory!=null)

  private val nodes = new ListBuffer[BasicBlock]
//  private val initialNodeFactory = new BasicBlockFactory(implementationFactory,noLocation,"$dummy")
//  private val initialNode = initialNodeFactory.basicBlock

  private var pStartNode :Option[BasicBlock] = None
  private var pEndNode  :Option[BasicBlock] = None

  private[implementations] def addNode(bb: BasicBlock) = {
    require(!(nodes contains bb))
    require(bb.cfg == this)
    nodes += bb
  }

  private[implementations] def setStartNode(bb: BasicBlock) = {
    require(nodes contains bb)
    pStartNode = Some(bb)
  }

  private[implementations] def setEndNode(bb: BasicBlock) = {
    require(nodes contains bb)
    pEndNode = Some(bb)
  }

  def startNode: BasicBlock = pStartNode match { case Some(n) => n case None => throw new Exception() }

  def endNode: BasicBlock = pEndNode match { case Some(n) => n  case None => throw new Exception() }

  override def toString = nodes.mkString("\n")
}