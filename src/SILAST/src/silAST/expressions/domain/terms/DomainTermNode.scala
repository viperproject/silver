package silAST.expressions.domain.terms

import silAST.expressions.domain.GDomainExpressionNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class DomainTermNode(sl : SourceLocation) extends GDomainTermNode[DomainTermNode](sl) {
}