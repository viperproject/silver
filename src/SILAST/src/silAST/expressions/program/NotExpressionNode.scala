package silAST.expressions.program
import silAST.expressions.TermNode
import silAST.source.SourceLocation

class NotExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		expression : ProgramExpressionNode[T]
    ) extends UnaryBooleanExpressionNode[T](sl, expression) 
{
	override def toString() : String = { return "!" + expression.toString()}
}