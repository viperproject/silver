package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.AssertionExpression
import silAST.expressions.terms.GTerm

abstract class GLogicalExpression[+T <: GTerm[T]]( sl : SourceLocation) extends AssertionExpression(sl) {

  def subExpressions(): Seq[GLogicalExpression[T]]

}