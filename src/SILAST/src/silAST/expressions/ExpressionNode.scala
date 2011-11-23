package silAST.expressions

import scala.collection.Seq
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

abstract class ExpressionNode[+T <: TermNode[T]](val sl : SourceLocation) extends ASTNode(sl) 
{
  def subExpressions : Seq[ExpressionNode[T]] 
}