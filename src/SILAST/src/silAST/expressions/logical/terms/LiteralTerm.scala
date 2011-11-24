package silAST.expressions.logical.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTerm
import silAST.expressions.program.terms.ProgramTerm
import silAST.expressions.domain.terms.GDomainTerm

abstract class LiteralTerm(sl:SourceLocation) 
	extends GLogicalTerm[LiteralTerm](sl) 
	with GProgramTerm[LiteralTerm]
	with GDomainTerm[LiteralTerm]
	with AtomicTerm[LiteralTerm]
{
}