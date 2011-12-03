package silAST.symbols

import silAST.ASTNode
import silAST.expressions.util.GenericExpressionSequence.ExpressionSequence
import silAST.source.SourceLocation

final class MethodSignature private[silAST](
    sl : SourceLocation,
    val parameters: ProgramVariableSequence,
    val result: ProgramVariable,
    val precondition: ExpressionSequence,
    val postcondition: ExpressionSequence
) extends ASTNode(sl)
{
  override def toString =
    "(" + parameters.toString + ") : " + result.toString +
      (for (p <- precondition ) yield "requires " + p.toString).mkString("\n") +
      (for (p <- postcondition) yield "ensures " + p.toString).mkString("\n")

  override def subNodes = parameters.variables.toList ++ (result :: (precondition.toList ++ postcondition.toList))
}