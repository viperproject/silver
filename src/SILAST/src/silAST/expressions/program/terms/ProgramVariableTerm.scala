package silAST.expressions.programs.terms
import silAST.AtomicNode
import silAST.symbols.ProgramVariable
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTerm
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.terms.AtomicTerm

class ProgramVariableTerm(
		sl : SourceLocation, 
		val variable : ProgramVariable 
	) 
	extends GLogicalTerm[ProgramVariableTerm](sl) 
	with GProgramTerm[ProgramVariableTerm]
	with AtomicTerm[ProgramVariableTerm]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
	override def subNodes : Seq[ASTNode] = { return variable :: Nil }
}