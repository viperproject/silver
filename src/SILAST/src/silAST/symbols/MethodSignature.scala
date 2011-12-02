package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.expressions.util.TermSequence
import silAST.source.SourceLocation
import silAST.programs.ProgramFactory

final class MethodSignature private[silAST](
    sl : SourceLocation,
    val parameters: ProgramVariableSequence,
    val result: ProgramVariable,
    val precondition: TermSequence,
    val postcondition: TermSequence
) extends ASTNode(sl)
{
  override def toString =
    "(" + parameters.toString + ") : " + result.toString +
      (for (p <- precondition ) yield "requires " + p.toString).mkString("\n") +
      (for (p <- postcondition) yield "ensures " + p.toString).mkString("\n")

  override def subNodes = parameters.variables.toList ++ (result :: (precondition.toList ++ postcondition.toList))
}