package silAST.expressions.program.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.Field
import silAST.expressions.GExpressionNode

class DereferenceTermNode[+T <: GProgramTermNode[T]](
    sl : SourceLocation, 
    val location : T, 
    val field : Field) 
  extends GProgramTermNode[T](sl) 
{

  override def toString(): String = { return location.toString() + "." + field.name }

  override def subNodes(): Seq[T] = { return location :: Nil }
  override def subTerms(): Seq[T] = { return location :: Nil }

}