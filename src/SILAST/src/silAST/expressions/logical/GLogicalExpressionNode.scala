package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.assertion.AssertionExpressionNode
import silAST.expressions.terms.GTermNode

abstract class GLogicalExpressionNode[+T <: GTermNode[T]]( sl : SourceLocation) extends AssertionExpressionNode(sl) {

  def subExpressions(): Seq[GLogicalExpressionNode[T]]

}