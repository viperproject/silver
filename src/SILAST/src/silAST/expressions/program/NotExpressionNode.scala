package silAST.expressions.program
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

class NotExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		expression : ProgramExpressionNode[T]
    ) extends UnaryBooleanExpressionNode[T](sl, expression) 
{
	override def toString() : String = { return "!" + expression.toString()}
}