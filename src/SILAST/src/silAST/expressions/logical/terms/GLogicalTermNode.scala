package silAST.expressions.logical.terms
import silAST.source.SourceLocation
import silAST.expressions.terms.GTermNode

abstract class GLogicalTermNode[+T <:GLogicalTermNode[T]](sl : SourceLocation) extends GTermNode[T](sl) {

}