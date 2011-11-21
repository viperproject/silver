package silAST.expressions.terms

import scala.collection.Seq
import symbols.DataType
import source.SourceLocation

class CastExpressionNode(
    sl:SourceLocation, 
    val expression:ExpressionNode, 
    val newType : DataType)
    extends ExpressionNode(sl) 
{
  assert(expression!=null);
  assert(newType   !=null);

  override def toString(): String = { return "(" + expression + ") : " + newType.toString() }

  override def subNodes(): Seq[ExpressionNode] = { return expression :: Nil }

}