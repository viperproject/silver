package silAST.expressions.domain.terms
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm
import silAST.expressions.program.terms.GProgramTerm
import silAST.expressions.terms.GAtomicTerm

abstract class LiteralTerm(sl:SourceLocation) 
	extends GTerm[LiteralTerm](sl) 
	with GProgramTerm[LiteralTerm]
	with GDomainTerm[LiteralTerm]
	with GAtomicTerm[LiteralTerm]
{
}