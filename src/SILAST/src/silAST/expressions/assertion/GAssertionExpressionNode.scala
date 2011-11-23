package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpressionNode
import silAST.expressions.logical.terms.LogicalTermNode
import silAST.expressions.logical.terms.GLogicalTermNode

abstract class GAssertionExpressionNode[+T <:GLogicalTermNode[T]](sl : SourceLocation) extends GExpressionNode[T](sl) {
  def subExpressions : Seq[GAssertionExpressionNode[T]] 
}