package silAST.expressions.domain.terms

import silAST.expressions.terms.AtomicTerm
import silAST.source.SourceLocation
import silAST.symbols.logical.BoundVariable
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm

class BoundVariableTerm(
		sl : SourceLocation, 
		val variable : BoundVariable 
	) 
	extends GLogicalTerm[BoundVariableTerm](sl)
	with GDomainTerm[BoundVariableTerm] 
	with AtomicTerm[BoundVariableTerm]
{
	assert(variable!=null);
	
	override def toString(): String = { return variable.name; }
	override def subNodes : Seq[ASTNode] = { return variable :: Nil }
}