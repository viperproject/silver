package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.AssertionExpressionNode

abstract class LogicalExpressionNode( sl : SourceLocation) extends AssertionExpressionNode(sl) {

  def subExpressions(): Seq[LogicalExpressionNode]

}