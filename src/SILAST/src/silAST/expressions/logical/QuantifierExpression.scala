package silAST.expressions.domain

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.BoundVariable
import silAST.symbols.logical.quantification.Quantifier
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm
import silAST.expressions.logical.GLogicalExpression

class QuantifierExpression[+T <:GLogicalTerm[T]](
		sl : SourceLocation,
		val quantifier : Quantifier,
		val variable   : BoundVariable,
		val expression : GLogicalExpression[T]
    )
	extends GLogicalExpression[T](sl) 
{
  override def toString() : String = 
  { 
		  return quantifier.toString() + " " + variable.name + " : " + variable.dataType.toString() + " :: (" + expression.toString() + ")"
  }
  
  override def subNodes : Seq[ASTNode] = { return quantifier :: variable :: expression :: Nil }
  override def subExpressions: Seq[GLogicalExpression[T]] = { return expression :: Nil }
}