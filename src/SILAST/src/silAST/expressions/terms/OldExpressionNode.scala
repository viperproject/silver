package silAST.expressions.terms

import scala.collection.Seq
import source.SourceLocation

class OldExpressionNode(
    sl:SourceLocation, 
    val expression : ExpressionNode
  ) extends ExpressionNode(sl) 
{
	assert(expression!=null);
	
	override def toString(): String = { return "old(" + expression.toString() + ")" }

	override def subNodes(): Seq[ExpressionNode] = { return expression :: Nil }

}