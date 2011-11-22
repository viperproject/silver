package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.BoundVariable
import silAST.symbols.logical.Quantifier

class QuantifierExpressionNode(
		sl : SourceLocation,
		val quantifier : Quantifier,
		val variable   : BoundVariable,
		val expression : LogicalExpressionNode
    )
	extends LogicalExpressionNode(sl) 
{
  override def toString() : String = 
  { 
		  return quantifier.toString() + " " + variable.name + " : " + variable.dataType.toString() + " :: (" + expression.toString() + ")"
  }
  
  override def subNodes() : Seq[LogicalExpressionNode] = { return expression :: Nil }
}