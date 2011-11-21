package silAST

import scala.collection.Seq
import symbols.FieldId

class DereferenceExpressionNode(
    sl : SourceLocation, 
    val location : ExpressionNode, 
    val field : FieldId) 
  extends ExpressionNode(sl) 
{

  override def toString(): String = { return location.toString() + "." + field.name }

  override def subNodes(): Seq[ExpressionNode] = { return location :: Nil }

}