package silAST.expressions

import scala.collection.Seq
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.GTermNode

abstract class GExpressionNode[+T <: GTermNode[T]](val sl : SourceLocation) extends ASTNode(sl)
{
  def subExpressions : Seq[GExpressionNode[T]] 
}