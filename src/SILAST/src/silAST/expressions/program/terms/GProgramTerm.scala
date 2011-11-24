package silAST.expressions.program.terms
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTerm

abstract trait GProgramTerm[+T <: GLogicalTerm[T]] extends GLogicalTerm[T] {

}