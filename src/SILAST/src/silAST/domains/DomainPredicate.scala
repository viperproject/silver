package silAST.domains

import silAST.source.SourceLocation
import silAST.{AtomicNode, ASTNode}
import silAST.expressions.util.TermSequence

class DomainPredicate private[silAST](
                                             sl: SourceLocation,
                                             val name: String,
                                             val signature: DomainPredicateSignature
                                             ) extends ASTNode(sl) with AtomicNode {
  override def toString = "predicate " + name + signature.toString
  def toString(ts : TermSequence) = name + ts.toString()

  override def subNodes = List(signature)
}