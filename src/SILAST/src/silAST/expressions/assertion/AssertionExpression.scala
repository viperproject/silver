package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpression
import silAST.expressions.logical.terms.LogicalTerm

abstract class AssertionExpression(sl : SourceLocation) extends GAssertionExpression[LogicalTerm](sl) {
  def subExpressions : Seq[AssertionExpression] 
}