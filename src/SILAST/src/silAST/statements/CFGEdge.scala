package silAST.statements

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.Expression

abstract class CFGEdge(
		sl : SourceLocation,
		val source : BasicBlock,
		val target : BasicBlock,
		val condition : Expression,
		val isBackEdge : Boolean
    )
    extends ASTNode(sl) 
{
}