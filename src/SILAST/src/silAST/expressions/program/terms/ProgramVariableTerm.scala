package silAST.expressions.programs.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTerm
import silAST.ASTNode
import silAST.expressions.assertion.terms.GTerm
import silAST.expressions.assertion.terms.GAtomicTerm

class ProgramVariableTerm(
		sl : SourceLocation, 
		val variable : ProgramVariable 
	) 
	extends GTerm[ProgramVariableTerm](sl) 
	with GProgramTerm[ProgramVariableTerm]
	with GAtomicTerm[ProgramVariableTerm]
{
	assert(variable!=null);
	
	override def toString : String = variable.name
	override def subNodes : Seq[ASTNode] = variable :: Nil
}