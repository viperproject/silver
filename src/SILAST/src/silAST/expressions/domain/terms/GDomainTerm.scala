package silAST.expressions.domain.terms
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.source.SourceLocation


abstract trait GDomainTerm[+T <: GLogicalTerm[T]] extends GLogicalTerm[T] {

}