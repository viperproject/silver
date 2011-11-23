package silAST.expressions.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.expressions.logical.LogicalTermNode
import silAST.symbols.logical.BoundVariable
import silAST.ASTNode

class BoundVariableNode(
		sl : SourceLocation, 
		val variable : BoundVariable 
	) 
	extends LogicalTermNode(sl) 
	with AtomicTermNode[BoundVariableNode]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
	override def subNodes : Seq[ASTNode] = { return variable :: Nil }
}