package silAST.methods

import silAST.ASTNode
import silAST.expressions.util.ExpressionSequence
import silAST.source.SourceLocation
import silAST.programs.symbols.ProgramVariableSequence

final class MethodSignature private[silAST](
                                             sl: SourceLocation,
                                             val parameters: ProgramVariableSequence,
                                             val results:    ProgramVariableSequence,
                                             val precondition: ExpressionSequence,
                                             val postcondition: ExpressionSequence
                                             ) extends ASTNode(sl) {
  override def toString =
    parameters.toString + " : " + results.toString + "\n" +
      (for (p <- precondition) yield "requires " + p.toString).mkString("\n") +
      (for (p <- postcondition) yield "ensures " + p.toString).mkString("\n")

  override def subNodes = parameters.variables.toList ++ List(results) ++ precondition.toList ++ postcondition.toList
}