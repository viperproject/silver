package silAST.methods.implementations

import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.source.{noLocation, SourceLocation}

final class ControlFlowGraph private[silAST](
                                              sl: SourceLocation,
                                              private val implementationFactory : ImplementationFactory
                                              ) extends ASTNode(sl) {
  //TODO: more consistency checks
  require(implementationFactory!=null)

  private val nodes = new ListBuffer[BasicBlock]
  private val initialNodeFactory = new BasicBlockFactory(implementationFactory,noLocation,"$dummy")
  private val initialNode = initialNodeFactory.basicBlock

  private var pStartNode = initialNode
  private var pEndNode = initialNode

  private[implementations] def addNode(bb: BasicBlock) = {
    require(!(nodes contains bb))
    require(bb.cfg == this)
    nodes += bb
  }

  private def eliminateInitialNodeIfNecessary() = {
    if (
      startNode != initialNode &&
        endNode != initialNode &&
        initialNode.statements.isEmpty &&
        initialNode.successors.isEmpty &&
        initialNode.predecessors.isEmpty
    )
      nodes.remove(0)

  }

  private[implementations] def setStartNode(bb: BasicBlock) = {
    require(nodes contains bb)
    pStartNode = bb
    eliminateInitialNodeIfNecessary()
  }

  private[implementations] def setEndNode(bb: BasicBlock) = {
    require(nodes contains bb)
    pEndNode = bb
    eliminateInitialNodeIfNecessary()
  }

  def startNode: BasicBlock = pStartNode

  def endNode: BasicBlock = pEndNode

  override def toString = nodes.mkString("\n")
}