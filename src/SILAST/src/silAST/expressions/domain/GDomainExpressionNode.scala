package silAST.expressions.domain

import scala.collection.Seq
import silAST.expressions.logical.GLogicalExpressionNode
import silAST.expressions.logical.terms.GLogicalTermNode
import silAST.source.SourceLocation
import silAST.expressions.program.GProgramExpressionNode

abstract class GDomainExpressionNode[+T <: GLogicalTermNode[T]](sl : SourceLocation) extends GLogicalExpressionNode[T](sl) {

  def subExpressions(): Seq[GLogicalExpressionNode[T]]

}