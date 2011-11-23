package silAST.expressions.programs.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation

class OldProgramVariable(
		sl : SourceLocation, 
		variable : ProgramVariable 
	) 
	extends ProgramVariableTerm(sl, variable) 
{
	assert(variable!=null);
	
	override def toString(): String = { return "old(" + variable.name + ")"; }
}