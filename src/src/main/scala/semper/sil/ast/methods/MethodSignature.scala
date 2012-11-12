package semper.sil.ast.methods

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.util.ExpressionSequence
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.programs.symbols.ProgramVariableSequence

final class MethodSignature private [sil](

                                             val parameters: ProgramVariableSequence,
                                             val results: ProgramVariableSequence,
                                             val precondition: ExpressionSequence,
                                             val postcondition: ExpressionSequence
                                             )(val sourceLocation: SourceLocation) extends ASTNode
{

  override val comment = Nil

  override def toString =
    parameters.toStringWithTypes + " : " + results.toStringWithTypes + "\n" +
      (for (p <- precondition) yield "requires " + p.toString).mkString("\t", "\n\t", "\n") +
      (for (p <- postcondition) yield "ensures " + p.toString).mkString("\t", "\n\t", "\n")

  override def equals(other: Any): Boolean = {
    other match {
      case s: MethodSignature =>
        parameters == s.parameters &&
          results == s.results &&
          precondition == s.precondition &&
          postcondition == s.postcondition

      case _ => false
    }
  }

  override def hashCode(): Int = parameters.hashCode() + results.hashCode() + precondition.hashCode() + postcondition.hashCode()
}