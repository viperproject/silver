package semper.sil.ast.domains

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.util.ExpressionSequence

trait DomainFunction extends ASTNode {
  def sourceLocation: SourceLocation

  def name: String

  def signature: DomainFunctionSignature

  def domain: GDomain

  def substitute(s: TypeVariableSubstitution): DomainFunction

  private[sil] def substituteI(s: TypeVariableSubstitution): DomainFunction

  def fullName = domain.fullName + "." + name

  override def toString = "function " + name + signature.toString

  def toString(args: ExpressionSequence) = fullName + args

  override def equals(other: Any): Boolean = {
    other match {
      case df: DomainFunction => this eq df
      case _ => false
    }
  }

  override def hashCode: Int = (fullName + signature.toString).hashCode()

}

final private[sil] class DomainFunctionC(
                                          val name: String,
                                          val signature: DomainFunctionSignature,
                                          val domain: GDomain
                                          )(val sourceLocation: SourceLocation, override val comment: List[String]) extends DomainFunction {
  override def substitute(s: TypeVariableSubstitution): DomainFunction =
    domain.substitute(s).functions.find(_.name == name).get

  private[sil] def substituteI(s: TypeVariableSubstitution): DomainFunction = {
    val result = new DomainFunctionC(name, signature.substitute(s), domain.substitute(s))(sourceLocation, Nil)
    result
  }
}