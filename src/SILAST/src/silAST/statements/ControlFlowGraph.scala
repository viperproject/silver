package silAST.statements

import silAST.ASTNode

abstract class ControlFlowGraph extends ASTNode
{
	val nodes : Set[BasicBlock]
	val startNode : BasicBlock
	val endNode   : BasicBlock
//	assert(nodes.contains(startNode))
//	assert(nodes.contains(endNode))
	//TODO: more consistency checks
}