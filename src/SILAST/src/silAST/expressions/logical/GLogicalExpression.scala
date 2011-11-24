package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.AssertionExpression
import silAST.expressions.logical.terms.GLogicalTerm

abstract class GLogicalExpression[+T <: GLogicalTerm[T]]( sl : SourceLocation) extends AssertionExpression(sl) {

  def subExpressions(): Seq[GLogicalExpression[T]]

}