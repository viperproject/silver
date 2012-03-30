package silAST.methods

import implementations.Implementation
import silAST.source.SourceLocation
import collection.Set
import collection.mutable.HashSet
import silAST.expressions.ExpressionFactory
import silAST.programs.symbols.ProgramVariable

final class Method private[silAST](

                                    val name: String,
                                    val signature: MethodSignature,
                                    override val factory: MethodFactory
                                    )(val sourceLocation: SourceLocation)
  extends Scope {
  override val parentScope = None

  def implementations: Set[Implementation] = pImplementations.toSet

  lazy val expressionFactory: ExpressionFactory = factory
  private[silAST] val pImplementations = new HashSet[Implementation]

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