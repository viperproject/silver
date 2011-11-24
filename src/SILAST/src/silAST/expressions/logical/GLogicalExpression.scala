package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.terms.GTerm
import silAST.expressions.assertion.GExpression

abstract class GLogicalExpression[+T <: GTerm[T]]( sl : SourceLocation) extends GExpression(sl) {
  def subExpressions : Seq[GLogicalExpression[T]]
}