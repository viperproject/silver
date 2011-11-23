package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.AssertionExpression

abstract class LogicalExpression( sl : SourceLocation) extends AssertionExpression(sl) {

  def subExpressions(): Seq[LogicalExpression]

}