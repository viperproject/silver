package semper.sil.ast.methods

import implementations.Implementation
import semper.sil.ast.source.SourceLocation
import collection.{mutable, Set}
import semper.sil.ast.expressions.ExpressionFactory
import semper.sil.ast.programs.symbols.ProgramVariable

final class Method private[sil](

                                 val name: String,
                                 val signature: MethodSignature,
                                 override val factory: MethodFactory
                                 )(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Scope {
  override val parentScope = None

  def implementations: Set[Implementation] = pImplementations.toSet

  lazy val expressionFactory: ExpressionFactory = factory
  private[sil] val pImplementations = new mutable.HashSet[Implementation]

  override def locals = signature.parameters.toSet[ProgramVariable] union signature.results.toSet

  override def programVariables: Set[ProgramVariable] =
    locals

  override def equals(other: Any): Boolean = {
    other match {
      case m: Method => this eq m
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()

  override def toString = "method " + name + signature.toString +
    (for (i <- implementations) yield i).mkString("\n", "\n", "\n")


}