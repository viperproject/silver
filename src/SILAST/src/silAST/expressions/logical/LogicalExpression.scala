package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.Expression

abstract trait LogicalExpression extends Expression {
  def subExpressions: Seq[LogicalExpression]
}