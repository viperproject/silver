package silAST.expressions.domain
import silAST.expressions.logical.terms.LogicalTermNode
import silAST.source.SourceLocation


abstract class DomainTermNode[+T <: DomainTermNode[T]](sl : SourceLocation) extends LogicalTermNode(sl) {

}