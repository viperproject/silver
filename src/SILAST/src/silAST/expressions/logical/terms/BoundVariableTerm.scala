package silAST.expressions.domain.terms

import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.BoundVariable
import silAST.ASTNode
import silAST.expressions.assertion.terms.GTerm
import silAST.expressions.assertion.terms.GAtomicTerm

class BoundVariableTerm(
		sl : SourceLocation, 
		val variable : BoundVariable 
	) 
	extends GTerm[BoundVariableTerm](sl)
	with GDomainTerm[BoundVariableTerm] 
	with GAtomicTerm[BoundVariableTerm]
{
	assert(variable!=null);
	
	override def toString : String = variable.name
	override def subNodes : Seq[ASTNode] = variable :: Nil
}