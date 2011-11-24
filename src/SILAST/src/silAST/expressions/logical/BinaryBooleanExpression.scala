package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.BinaryBooleanOperator
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm

class BinaryBooleanExpression[+T <: GLogicalTerm[T]](
		sl : SourceLocation,
		val operator : BinaryBooleanOperator,
		val expression1 : GProgramExpression[T],
		val expression2 : GProgramExpression[T]
    )
    extends GProgramExpression[T](sl) {

	override def toString() : String = { return expression1.toString() + " " + operator.toString() + " " + expression2.toString()}
	
	override def subNodes(): Seq[ASTNode] = { return expression1 :: (operator :: (expression2 :: Nil)) }
	override def subExpressions(): Seq[GProgramExpression[T]] = { return expression1 :: expression2 :: Nil }

}