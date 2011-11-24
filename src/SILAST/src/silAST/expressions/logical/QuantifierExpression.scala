package silAST.expressions.domain

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.BoundVariable
import silAST.symbols.logical.quantification.Quantifier
import silAST.ASTNode
import silAST.expressions.logical.GLogicalExpression
import silAST.expressions.assertion.terms.GTerm

class QuantifierExpression[+T <:GTerm[T]](
		sl : SourceLocation,
		val quantifier : Quantifier,
		val variable   : BoundVariable,
		val expression : GLogicalExpression[T]
    )
	extends GLogicalExpression[T](sl) 
	with GDomainExpression[T]
{
  override def toString : String = quantifier.toString + " " + variable.name + " : " + variable.dataType.toString + " :: (" + expression.toString + ")"
  
  override def subNodes : Seq[ASTNode] = quantifier :: variable :: expression :: Nil
  override def subExpressions: Seq[GLogicalExpression[T]] = expression :: Nil
}