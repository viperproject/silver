package silAST.domains

import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.expressions.util.TermSequence

trait DomainPredicate extends ASTNode
{
  def name: String
  def signature: DomainPredicateSignature
  def domain : Domain

  lazy val fullName = domain.fullName + "." + name

  override def toString = "predicate " + name + signature.toString
  def toString(ts : TermSequence) = fullName + ts.toString()
  def substitute(s: TypeVariableSubstitution) : DomainPredicate

  override def equals(other : Any) : Boolean =
  {
    other match{
      case p : DomainPredicate => this eq p
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()

}

class DomainPredicateC private[silAST](

                                             val name: String,
                                             val signature: DomainPredicateSignature,
                                             val domain : Domain
                                             )(val sourceLocation : SourceLocation) extends DomainPredicate
{
  def substitute(s: TypeVariableSubstitution) =
    new DomainPredicateC(name,signature.substitute(s),s.newDomain)(sourceLocation)
}