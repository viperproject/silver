package silAST.expressions.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.expressions.program.ProgramTermNode

class ProgramVariableNode(
		sl : SourceLocation, 
		val variable : ProgramVariable 
	) 
	extends ProgramTermNode(sl) 
	with AtomicNode[ProgramVariableNode]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
}