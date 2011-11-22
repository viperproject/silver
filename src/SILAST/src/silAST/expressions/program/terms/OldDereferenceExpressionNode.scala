package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.Field

class OldDereferenceTermNode[+T <: TermNode[T]](
    sl : SourceLocation, 
    val location : T, 
    val field : Field) 
  extends ExpressionNode(sl) 
{

  override def toString(): String = { return location.toString() + "._(old)" + field.name }

  override def subNodes(): Seq[T] = { return location :: Nil }

}