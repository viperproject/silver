package silAST.expressions

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.terms.GTerm

abstract class GExpression[+T <:GTerm[T]](sl : SourceLocation) extends Expression(sl) {
  def subExpressions : Seq[GExpression[T]] 
}
