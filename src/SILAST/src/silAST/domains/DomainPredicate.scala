package silAST.domains

import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.expressions.util.TermSequence

class DomainPredicate private[silAST](
                                             sl: SourceLocation,
                                             val name: String,
                                             val signature: DomainPredicateSignature
                                             ) extends ASTNode(sl) {
  def substitute(s: TypeSubstitution) = new DomainPredicate(sl,name,signature.substitute(s))

  override def toString = "predicate " + name + signature.toString
  def toString(ts : TermSequence) = name + ts.toString()
}