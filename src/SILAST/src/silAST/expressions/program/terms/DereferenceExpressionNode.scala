package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.Field
import silAST.expressions.ExpressionNode

class DereferenceTermNode[+T <: TermNode[T]](
    sl : SourceLocation, 
    val location : T, 
    val field : Field) 
  extends TermNode[T](sl) 
{

  override def toString(): String = { return location.toString() + "." + field.name }

  override def subNodes(): Seq[T] = { return location :: Nil }
  override def subTerms(): Seq[T] = { return location :: Nil }

}