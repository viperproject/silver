package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.Field
import silAST.expressions.ExpressionNode
import silAST.expressions.program.terms.ProgramTermNode

class OldDereferenceTermNode[+T <: TermNode[T]](
    sl : SourceLocation, 
    val location : T, 
    val field : Field) 
  extends ProgramTermNode[T](sl) 
{

  override def toString(): String = { return location.toString() + "._(old)" + field.name }

  override def subNodes : Seq[T] = { return location :: Nil }
  override def subTerms : Seq[T] = { return location :: Nil }

}