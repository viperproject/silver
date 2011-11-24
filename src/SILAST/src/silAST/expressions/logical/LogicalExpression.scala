package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.Expression

abstract class LogicalExpression( sl : SourceLocation) extends Expression(sl) {

  def subExpressions(): Seq[LogicalExpression]

}