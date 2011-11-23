package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.Field
import silAST.expressions.GExpressionNode
import silAST.expressions.program.terms.GProgramTermNode
import silAST.expressions.logical.terms.GLogicalTermNode

class OldDereferenceTermNode[+T <: GLogicalTermNode[T]](
    sl : SourceLocation, 
    val location : T, 
    val field : Field) 
  extends GProgramTermNode[T](sl) 
{

  override def toString(): String = { return location.toString() + "._(old)" + field.name }

  override def subNodes : Seq[T] = { return location :: Nil }
  override def subTerms : Seq[T] = { return location :: Nil }

}