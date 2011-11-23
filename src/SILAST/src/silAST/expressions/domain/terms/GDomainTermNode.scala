package silAST.expressions.domain.terms
import silAST.expressions.logical.terms.GLogicalTermNode
import silAST.source.SourceLocation


abstract class GDomainTermNode[+T <: GLogicalTermNode[T]](sl : SourceLocation) extends GLogicalTermNode[T](sl) {

}