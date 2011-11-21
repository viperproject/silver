package silAST
import symbols.ProgramVariable

class ProgramVariableNode(sl : SourceLocation, val variable : ProgramVariable ) 
	extends ExpressionNode(sl) 
	with AtomicNode
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
}