package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.util.TermSequence

class DomainFunction private[silAST](
                                            sl: SourceLocation,
                                            val name: String,
                                            val signature: DomainFunctionSignature
                                            ) extends ASTNode(sl)
{
  def substitute(s: TypeSubstitution) : DomainFunction = new DomainFunction(sl,name,signature.substitute(s))

  override def toString = "function " + name + signature.toString

  def toString(args : TermSequence) = name + args
}