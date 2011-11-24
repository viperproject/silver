package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.domain.GDomainExpression
import silAST.expressions.program.GProgramExpression

class EqualityExpression[+T <: GLogicalTerm[T]](
    sl : SourceLocation, 
    val expression1 : T,
    val expression2 : T)
    extends GLogicalExpression[T](sl) with GDomainExpression[T] with GProgramExpression[T] 
{

  override def toString(): String = { return expression1.toString() + "=" + expression2.toString() }

  override def subNodes(): Seq[T] = { expression1 :: expression2 :: Nil }
  override def subExpressions: Seq[GLogicalExpression[T]] = { Nil }

}