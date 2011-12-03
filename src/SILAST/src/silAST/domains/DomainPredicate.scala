package silAST.domains

import silAST.source.SourceLocation
import silAST.{AtomicNode, ASTNode}
import silAST.symbols.DomainPredicateSignature

final class DomainPredicate private[silAST](
                                             sl: SourceLocation,
                                             val name: String,
                                             val signature: DomainPredicateSignature
                                             ) extends ASTNode(sl) with AtomicNode {
  override def toString = "predicate " + name + signature.toString

  override def subNodes = Nil
}