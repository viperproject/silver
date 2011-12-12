package silAST.methods

import silAST.ASTNode
import silAST.expressions.util.ExpressionSequence
import silAST.source.SourceLocation
import silAST.programs.symbols.ProgramVariableSequence

final class MethodSignature private[silAST](
                                             sl: SourceLocation,
                                             val parameters: ProgramVariableSequence,
                                             val results: ProgramVariableSequence,
                                             val precondition: ExpressionSequence,
                                             val postcondition: ExpressionSequence
                                             ) extends ASTNode(sl) {
  override def toString =
    parameters.toStringWithTypes + " : " + results.toStringWithTypes + "\n" +
      (for (p <- precondition) yield "requires " + p.toString).mkString("\t", "\n\t", "\n") +
      (for (p <- postcondition) yield "ensures " + p.toString).mkString("\t", "\n\t", "\n")

}