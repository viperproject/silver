package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.util.TermSequence

trait DomainFunction extends ASTNode {
  def sourceLocation: SourceLocation

  def name: String

  def signature: DomainFunctionSignature

  def domain: GDomain

  def substitute(s: TypeVariableSubstitution): DomainFunction

  def fullName = domain.fullName + "." + name

  override def toString = "function " + name + signature.toString

  def toString(args: TermSequence) = fullName + args

  override def equals(other: Any): Boolean = {
    other match {
      case df: DomainFunction => this eq df
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()

}

final private[silAST] class DomainFunctionC(
                                             val name: String,
                                             val signature: DomainFunctionSignature,
                                             val domain: GDomain
                                             )(val sourceLocation: SourceLocation) extends DomainFunction {
  override def substitute(s: TypeVariableSubstitution): DomainFunction = {
    new DomainFunctionC(name, signature.substitute(s), s.newDomain)(sourceLocation)
  }
}