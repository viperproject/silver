package silAST.expressions.program.terms
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm

abstract trait GProgramTerm[+T <: GTerm[T]] extends GTerm[T] {

}