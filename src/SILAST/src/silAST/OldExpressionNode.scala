package silAST

import scala.collection.Seq

class OldExpressionNode(
    sl:SourceLocation, 
    val expression : ExpressionNode
  ) extends ExpressionNode(sl) 
{
	assert(expression!=null);
	
	override def toString(): String = { return "old(" + expression.toString() + ")" }

	override def subNodes(): Seq[ExpressionNode] = { return expression :: Nil }

}