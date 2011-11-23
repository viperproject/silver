package silAST.expressions.program.terms
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTermNode
import silAST.expressions.terms.GTermNode

abstract class GProgramTermNode[+T <: GLogicalTermNode[T]](sl : SourceLocation) extends GLogicalTermNode[T](sl) {

}