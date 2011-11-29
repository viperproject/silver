package silAST.statements

import silAST.ASTNode
import silAST.source.SourceLocation

abstract class ControlFlowGraph( sl : SourceLocation) extends ASTNode(sl) {
  val nodes: Set[BasicBlock]
  val startNode: BasicBlock
  val endNode: BasicBlock
  //	assert(nodes.contains(startNode))
  //	assert(nodes.contains(endNode))
  //TODO: more consistency checks
}