package silAST.domains

import silAST.ASTNode
import silAST.expressions.DExpression
import silAST.source.SourceLocation

final class DomainAxiom private[silAST](
                                         val sourceLocation : SourceLocation,
                                         val name: String,
                                         val expression: DExpression
                                         ) extends ASTNode {
  def substitute(ts: TypeSubstitution) : DomainAxiom =
    new DomainAxiom(sourceLocation,name,expression.substitute(new DLogicalVariableSubstitutionC(ts.types,Set(),ts.newDomain)))

  override def toString = "axiom " + name + " = " + expression.toString
}