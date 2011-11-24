package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpression
import silAST.expressions.logical.terms.LogicalTerm
import silAST.expressions.logical.terms.GLogicalTerm

abstract class GAssertionExpression[+T <:GLogicalTerm[T]](sl : SourceLocation) extends GExpression[T](sl) {
  def subExpressions : Seq[GAssertionExpression[T]] 
}