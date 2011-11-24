package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.BinaryBooleanOperator
import silAST.ASTNode
import silAST.expressions.assertion.terms.GTerm

class BinaryBooleanExpression[+T <: GTerm[T]](
		sl : SourceLocation,
		val operator : BinaryBooleanOperator,
		val expression1 : GLogicalExpression[T],
		val expression2 : GLogicalExpression[T]
    )
    extends GLogicalExpression[T](sl) 
{

	override def toString : String = expression1.toString + " " + operator.toString + " " + expression2.toString
	
	override def subNodes : Seq[ASTNode] = expression1 :: (operator :: (expression2 :: Nil))
	override def subExpressions: Seq[GLogicalExpression[T]] = expression1 :: expression2 :: Nil

}