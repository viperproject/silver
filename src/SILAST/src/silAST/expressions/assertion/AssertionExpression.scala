package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.logical.terms.LogicalTermTrait
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.logical.terms.LogicalTermTrait

abstract class AssertionExpression(sl : SourceLocation) extends GAssertionExpression[GLogicalTerm[LogicalTermTrait]](sl) {
  type LogicalTerm = GLogicalTerm[LogicalTermTrait]
  def subExpressions : Seq[AssertionExpression] 
}