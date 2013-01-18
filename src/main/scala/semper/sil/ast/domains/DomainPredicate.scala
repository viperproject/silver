package semper.sil.ast.domains

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.util.ExpressionSequence

trait DomainPredicate extends ASTNode {
  def name: String

  def signature: DomainPredicateSignature

  def domain: GDomain

  lazy val fullName = domain.fullName + "." + name

  override def toString = "predicate " + name + signature.toString

  def toString(ts: ExpressionSequence) = fullName + ts.toString()

  def substitute(s: TypeVariableSubstitution): DomainPredicate

  private[sil] def substituteI(s: TypeVariableSubstitution): DomainPredicate

  override def equals(other: Any): Boolean = {
    other match {
      case p: DomainPredicate => this eq p
      case _ => false
    }
  }

  override def hashCode: Int = (fullName + signature.toString).hashCode()

}

class DomainPredicateC private[sil](
                                     val name: String,
                                     val signature: DomainPredicateSignature,
                                     val domain: GDomain
                                     )(val sourceLocation: SourceLocation, override val comment: List[String]) extends DomainPredicate {
  def substitute(s: TypeVariableSubstitution) =
    domain.substitute(s).predicates.find(_.name == name).get

  def substituteI(s: TypeVariableSubstitution) =
    new DomainPredicateC(name, signature.substitute(s), domain.substitute(s))(sourceLocation, Nil)
}