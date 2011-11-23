package silAST.expressions

import scala.collection.Seq
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm

abstract class GExpression[+T <: GTerm[T]](val sl : SourceLocation) extends ASTNode(sl)
{
  def subExpressions : Seq[GExpression[T]] 
}