package silAST.expressions

import scala.collection.Seq
import silAST.expressions.terms.ExpressionNode
import silAST.source.SourceLocation

abstract class TermNode[+T <: TermNode[T]](sl:SourceLocation) extends ExpressionNode[T](sl) {

  def subNodes(): Seq[T]

}