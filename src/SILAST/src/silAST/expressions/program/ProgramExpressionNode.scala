package silAST.expressions.program

import scala.collection.Seq
import silAST.expressions.logical.LogicalExpressionNode
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

abstract class ProgramExpressionNode[+T <: TermNode[T]]( 
		sl : SourceLocation 
		) 
		extends LogicalExpressionNode(sl) 
{
  def subExpressions(): Seq[ProgramExpressionNode[T]]
}