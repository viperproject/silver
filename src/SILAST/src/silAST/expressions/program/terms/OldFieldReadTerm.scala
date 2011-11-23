package silAST.expressions.terms

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.Field
import silAST.expressions.GExpression
import silAST.expressions.program.terms.GProgramTerm
import silAST.expressions.logical.terms.GLogicalTerm

class OldFieldReadTerm[+T <: GLogicalTerm[T]](
    sl : SourceLocation, 
    val location : T, 
    val field : Field) 
  extends GLogicalTerm[T](sl) with GProgramTerm[T] 
{

  override def toString(): String = { return location.toString() + "._(old)" + field.name }

  override def subNodes : Seq[T] = { return location :: Nil }
  override def subTerms : Seq[T] = { return location :: Nil }

}