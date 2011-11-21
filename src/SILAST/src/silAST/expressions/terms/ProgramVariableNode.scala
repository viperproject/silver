package silAST.expressions.terms
import symbols.ProgramVariable
import silAST.AtomicNode
import source.SourceLocation

class ProgramVariableNode(sl : SourceLocation, val variable : ProgramVariable ) 
	extends ExpressionNode(sl) 
	with AtomicNode
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
}