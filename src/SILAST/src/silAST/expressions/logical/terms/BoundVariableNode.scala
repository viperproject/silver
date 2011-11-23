package silAST.expressions.logical.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.symbols.logical.BoundVariable
import silAST.ASTNode
import silAST.expressions.terms.AtomicTermNode

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