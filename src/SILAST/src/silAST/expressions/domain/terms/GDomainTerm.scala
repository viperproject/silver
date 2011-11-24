package silAST.expressions.domain.terms
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm


abstract trait GDomainTerm[+T <: GTerm[T]] extends GTerm[T] {

}