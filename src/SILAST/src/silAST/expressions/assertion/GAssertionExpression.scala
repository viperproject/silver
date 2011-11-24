package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.LogicalTermTrait
import silAST.expressions.logical.terms.GLogicalTerm

abstract class GAssertionExpression[+T <:GLogicalTerm[T]](sl : SourceLocation) extends ASTNode(sl) {
  def subExpressions : Seq[GAssertionExpression[T]] 
}