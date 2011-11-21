package silAST.expressions.terms

import scala.collection.Seq
import source.SourceLocation

class EqualityExpressionNode(
    sl : SourceLocation, 
    val expression1 : ExpressionNode,
    val expression2 : ExpressionNode)
    extends ExpressionNode(sl) {

  override def toString(): String = { return expression1.toString() + "=" + expression2.toString() }

  override def subNodes(): Seq[ExpressionNode] = { expression1 :: expression2 :: Nil }

}