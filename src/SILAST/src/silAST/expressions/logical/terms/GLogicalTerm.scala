package silAST.expressions.logical.terms
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm

abstract class GLogicalTerm[+T <:GLogicalTerm[T]](sl : SourceLocation) extends GTerm[T](sl) {

}