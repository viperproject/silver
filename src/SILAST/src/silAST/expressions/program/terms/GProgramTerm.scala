package silAST.expressions.program.terms
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.terms.GTerm

abstract trait GProgramTerm[+T <: GLogicalTerm[T]] extends GLogicalTerm[T] {

}