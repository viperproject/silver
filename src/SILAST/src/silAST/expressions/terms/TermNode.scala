package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.ExpressionNode

abstract class TermNode[+T <: TermNode[T]](sl:SourceLocation) extends ExpressionNode[T](sl) {

  def subTerms(): Seq[T]

}