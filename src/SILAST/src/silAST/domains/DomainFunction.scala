package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.util.TermSequence
import silAST.types.TypeVariable

trait DomainFunction extends ASTNode
{
  def sourceLocation : SourceLocation
  def name: String
  def signature: DomainFunctionSignature
  def domain : Domain

  def substitute(s: TypeSubstitution) : DomainFunction

  def fullName = domain.fullName + "." + name
  override def toString = "function " + name + signature.toString

  def toString(args : TermSequence) = fullName + args

  override def equals(other : Any) : Boolean =
  {
    other match{
      case df : DomainFunction => this eq df
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()

}

final private[silAST] class DomainFunctionC(
                                      val sourceLocation : SourceLocation,
                                      val name: String,
                                      val signature: DomainFunctionSignature,
                                      val domain : Domain
                                      ) extends DomainFunction
{
  override def substitute(s: TypeSubstitution) : DomainFunction ={
    new DomainFunctionC(sourceLocation,name,signature.substitute(s), s.newDomain)
  }
}