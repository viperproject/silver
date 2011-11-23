package silAST.expressions.domain

import scala.collection.Seq
import silAST.expressions.domain.terms.DomainTermNode
import silAST.source.SourceLocation

abstract class DomainExpressionNode(sl : SourceLocation) extends GDomainExpressionNode[DomainTermNode](sl) {
}