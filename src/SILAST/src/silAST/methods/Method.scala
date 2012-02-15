package silAST.methods

import implementations.Implementation
import silAST.ASTNode
import silAST.source.SourceLocation
import collection.Set
import collection.mutable.HashSet
import silAST.expressions.ExpressionFactory

final class Method private[silAST](
                                    val sourceLocation : SourceLocation,
                                    val name: String,
                                    val signature: MethodSignature,
                                    private[silAST] val factory : MethodFactory
                                    ) extends ASTNode {
  override def toString = "method " + name + signature.toString +
    (for (i <- implementations) yield i).mkString("\n","\n","\n")


  private[silAST] val pImplementations = new HashSet[Implementation]

  def implementations: Set[Implementation] = pImplementations.toSet

  lazy val expressionFactory : ExpressionFactory = factory

  override def equals(other : Any) : Boolean = {
    other match{
      case m : Method => this eq  m
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}