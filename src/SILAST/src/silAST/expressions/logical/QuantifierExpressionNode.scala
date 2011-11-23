package silAST.expressions.domain

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.BoundVariable
import silAST.symbols.logical.Quantifier
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTermNode
import silAST.expressions.logical.GLogicalExpressionNode

class QuantifierExpressionNode[+T <:GLogicalTermNode[T]](
		sl : SourceLocation,
		val quantifier : Quantifier,
		val variable   : BoundVariable,
		val expression : GLogicalExpressionNode[T]
    )
	extends GLogicalExpressionNode[T](sl) 
{
  override def toString() : String = 
  { 
		  return quantifier.toString() + " " + variable.name + " : " + variable.dataType.toString() + " :: (" + expression.toString() + ")"
  }
  
  override def subNodes : Seq[ASTNode] = { return quantifier :: variable :: expression :: Nil }
  override def subExpressions: Seq[GLogicalExpressionNode[T]] = { return expression :: Nil }
}