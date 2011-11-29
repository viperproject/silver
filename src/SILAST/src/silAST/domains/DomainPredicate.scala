package silAST.domains

import silAST.source.SourceLocation
import silAST.{AtomicNode, ASTNode}

final class DomainPredicate private[silAST](
  sl : SourceLocation,
  val name: String
) extends ASTNode(sl) with AtomicNode
{
  override def toString = "predicate " + name
  override def subNodes = Nil
}