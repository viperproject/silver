package silAST.expressions.program

import scala.collection.Seq
import silAST.expressions.logical.LogicalExpressionNode
import silAST.source.SourceLocation
import silAST.expressions.terms.GTermNode
import silAST.expressions.logical.GLogicalExpressionNode

abstract class GProgramExpressionNode[+T <: GTermNode[T]]( 
		sl : SourceLocation 
	) 
	extends GLogicalExpressionNode[T](sl) 
{
  def subExpressions(): Seq[GLogicalExpressionNode[T]]
}