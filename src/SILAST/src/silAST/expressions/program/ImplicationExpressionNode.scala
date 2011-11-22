package silAST.expressions.program
import silAST.expressions.TermNode
import silAST.source.SourceLocation

class ImplicationExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		expression1 : ProgramExpressionNode[T],
		expression2 : ProgramExpressionNode[T]
    ) extends BinaryBooleanExpressionNode[T](sl, expression1, expression2) 
{
  def operatorName() : String = { return "=>" }
}