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
  def substitute(s: TypeSubstitution) : DomainPredicate
}

class DomainPredicateC private[silAST](
                                             val sourceLocation : SourceLocation,
                                             val name: String,
                                             val signature: DomainPredicateSignature,
                                             val domain : Domain
                                             ) extends DomainPredicate
{
  def substitute(s: TypeSubstitution) =
    new DomainPredicateC(sourceLocation,name,signature.substitute(s),s.newDomain)
}