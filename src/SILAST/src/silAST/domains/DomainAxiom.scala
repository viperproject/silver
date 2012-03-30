package silAST.domains

import silAST.ASTNode
import silAST.expressions.DExpression
import silAST.source.SourceLocation

final class DomainAxiom private[silAST](

                                         val name: String,
                                         val expression: DExpression
                                         )
  (val sourceLocation : SourceLocation)
  extends ASTNode {
  def substitute(ts: TypeVariableSubstitution) : DomainAxiom =
    new DomainAxiom(
      name,
      expression.substitute(new DLogicalVariableSubstitutionC(ts.types,Set()))
    ) (sourceLocation)


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