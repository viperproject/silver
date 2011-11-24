package silAST.expressions.assertion

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.BinaryBooleanOperator
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm

sealed abstract class BinaryBooleanExpression[+T <: GLogicalTerm[T]](
		sl : SourceLocation,
		val expression1 : GExpression[T],
		val expression2 : GExpression[T]
    )
    extends GExpression[T](sl) {

	override def operator : BinaryBooleanOperator
	override def toString : String = { return expression1.toString() + " " + operator.toString() + " " + expression2.toString()}
	
	override def subNodes: Seq[ASTNode] = { return expression1 :: (operator :: (expression2 :: Nil)) }
	override def subExpressions: Seq[GExpression[T]] = { return expression1 :: expression2 :: Nil }
}