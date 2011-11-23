package silAST.expressions.domain.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.ExpressionNode
import silAST.expressions.terms.TermNode

class EqualityExpressionNode[+T <: TermNode[T]](
    sl : SourceLocation, 
    val expression1 : T,
    val expression2 : T)
    extends ExpressionNode[T](sl) {

  override def toString(): String = { return expression1.toString() + "=" + expression2.toString() }

  override def subNodes(): Seq[T] = { expression1 :: expression2 :: Nil }
  override def subExpressions(): Seq[ExpressionNode[T]] = { Nil }

}