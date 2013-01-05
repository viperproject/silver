package semper.sil.ast.domains

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.Expression
import semper.sil.ast.source.SourceLocation

final class DomainAxiom private[sil](

                                      val name: String,
                                      val expression: Expression
                                      )
                                    (val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode {
  def substitute(ts: TypeVariableSubstitution): DomainAxiom =
    new DomainAxiom(
      name,
      expression.substitute(new LogicalVariableSubstitutionC(ts.types, Set()))
    )(sourceLocation, Nil)


  override def toString = "axiom " + name + " = " + expression.toString

  override def equals(other: Any): Boolean = {
    other match {
      case a: DomainAxiom => this eq a
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}