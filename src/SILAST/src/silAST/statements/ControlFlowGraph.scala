package silAST.statements

import silAST.ASTNode
import silAST.source.SourceLocation

final class ControlFlowGraph private[silAST](
  sl : SourceLocation,
  val nodes: Set[BasicBlock],
  val startNode: BasicBlock,
  val endNode: BasicBlock
) extends ASTNode(sl)
{
  //	assert(nodes.contains(startNode))
  //	assert(nodes.contains(endNode))
  //TODO: more consistency checks

  override def subNodes = nodes.toSeq
  override def toString = nodes.mkString("\n")
}