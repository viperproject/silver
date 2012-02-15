package silAST.domains

import silAST.ASTNode
import silAST.expressions.DExpression
import silAST.source.SourceLocation
import silAST.types.TypeVariable

final class DomainAxiom private[silAST](
                                         val sourceLocation : SourceLocation,
                                         val name: String,
                                         val expression: DExpression
                                         ) extends ASTNode {
  def substitute(ts: TypeSubstitution) : DomainAxiom =
    new DomainAxiom(sourceLocation,name,expression.substitute(new DLogicalVariableSubstitutionC(ts.types,Set(),ts.newDomain)))

  override def toString = "axiom " + name + " = " + expression.toString

  override def equals(other : Any) : Boolean =
  {
    other match{
      case a : DomainAxiom => this eq a
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}