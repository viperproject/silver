package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

abstract class BinaryBooleanExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		val expression1 : ProgramExpressionNode[T],
		val expression2 : ProgramExpressionNode[T]
    )
    extends ProgramExpressionNode[T](sl) {

	def operatorName() : String
	
	override def toString() : String = { return expression1.toString() + " " + operatorName + " " + expression2.toString()}
	
	override def subNodes(): Seq[ProgramExpressionNode[T]] = { return expression1 :: expression2 :: Nil }

}