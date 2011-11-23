package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation

abstract class TermNode[+T <: TermNode[T]](sl:SourceLocation) extends ExpressionNode[T](sl) {

  def subTerms(): Seq[T]

}