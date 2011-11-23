package silAST.expressions.logical.terms

import silAST.expressions.terms.AtomicTermNode
import silAST.source.SourceLocation
import silAST.symbols.logical.BoundVariable
import silAST.ASTNode

class BoundVariableNode(
		sl : SourceLocation, 
		val variable : BoundVariable 
	) 
	extends GLogicalTermNode[BoundVariableNode](sl) 
	with AtomicTermNode[BoundVariableNode]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
	override def subNodes : Seq[ASTNode] = { return variable :: Nil }
}