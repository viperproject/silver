package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.GExpressionNode
import silAST.expressions.terms.GTermNode
import silAST.expressions.logical.terms.GLogicalTermNode

class EqualityExpressionNode[+T <: GLogicalTermNode[T]](
    sl : SourceLocation, 
    val expression1 : T,
    val expression2 : T)
    extends GLogicalExpressionNode[T](sl) {

  override def toString(): String = { return expression1.toString() + "=" + expression2.toString() }

  override def subNodes(): Seq[T] = { expression1 :: expression2 :: Nil }
  override def subExpressions: Seq[GLogicalExpressionNode[T]] = { Nil }

}