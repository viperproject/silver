package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpressionNode
import silAST.expressions.logical.terms.LogicalTermNode

abstract class AssertionExpressionNode(sl : SourceLocation) extends GAssertionExpressionNode[LogicalTermNode](sl) {
  def subExpressions : Seq[AssertionExpressionNode] 
}