package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.expressions.util.ExpressionSequence
import silAST.source.SourceLocation
import silAST.programs.ProgramFactory

final class MethodSignature private[silAST](
    sl : SourceLocation,
    private [silAST] val programFactory : ProgramFactory,
    val parameters: ProgramVariableSequence,
    val result: ProgramVariable,
    val precondition: ExpressionSequence,
    val postcondition: ExpressionSequence
) extends ASTNode(sl,programFactory)
{
  override def toString =
    "(" + parameters.toString + ") : " + result.toString +
      (for (p <- precondition.asSeq ) yield "requires " + p.toString).mkString("\n") +
      (for (p <- postcondition.asSeq) yield "ensures " + p.toString).mkString("\n")

  override def subNodes = parameters.variables.toList ++ (result :: (precondition.asSeq ++ postcondition.asSeq))
}