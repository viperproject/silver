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
  override def toString = "function " + name + signature.toString

  override def subNodes = List(signature)

  def toString(args : TermSequence) = name + args
}