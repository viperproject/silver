package silAST.expressions.program

import scala.collection.Seq
import silAST.expressions.logical.LogicalExpression
import silAST.source.SourceLocation
import silAST.expressions.logical.GLogicalExpression
import silAST.expressions.logical.terms.GLogicalTerm

abstract class GProgramExpression[+T <: GLogicalTerm[T]]( 
		sl : SourceLocation 
	) 
	extends GLogicalExpression[T](sl) 
{
  def subExpressions(): Seq[GLogicalExpression[T]]
}