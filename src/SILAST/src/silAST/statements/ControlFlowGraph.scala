package silAST.statements

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class ControlFlowGraph(
		sl : SourceLocation,
		val nodes : Set[BasicBlock],
		val startNode : BasicBlock,
		val endNode   : BasicBlock
	)
    extends ASTNode(sl) 
{
	assert(nodes.contains(startNode))
	assert(nodes.contains(endNode))
	//TODO: more consistency checks
}