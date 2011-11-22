package silAST.expressions.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.expressions.logical.LogicalTermNode
import silAST.symbols.logical.BoundVariable

class BoundVariableNode(
		sl : SourceLocation, 
		val variable : BoundVariable 
	) 
	extends LogicalTermNode(sl) 
	with AtomicNode[ProgramVariableNode]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
}