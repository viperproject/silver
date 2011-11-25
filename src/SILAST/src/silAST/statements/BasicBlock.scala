package silAST.statements

import scala.collection.Seq
import silAST.ASTNode
import silAST.source.SourceLocation

abstract class BasicBlock(
		sl : SourceLocation,
		val statements : Seq[Statement],
		val predecessors : Set[CFGEdge],
		val successors : Set[CFGEdge]
    ) 
    extends ASTNode(sl) 
{
}
