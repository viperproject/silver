package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode
import silAST.symbols.logical.BinaryBooleanOperator
import silAST.ASTNode

class BinaryBooleanExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		val operator : BinaryBooleanOperator,
		val expression1 : ProgramExpressionNode[T],
		val expression2 : ProgramExpressionNode[T]
    )
    extends ProgramExpressionNode[T](sl) {

	override def toString() : String = { return expression1.toString() + " " + operator.toString() + " " + expression2.toString()}
	
	override def subNodes(): Seq[ASTNode] = { return expression1 :: (operator :: (expression2 :: Nil)) }

}