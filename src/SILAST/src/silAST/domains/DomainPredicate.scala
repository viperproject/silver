package silAST.domains

import silAST.source.SourceLocation
import silAST.{AtomicNode, ASTNode}

class DomainPredicate private[silAST](
  sl : SourceLocation,
  val name: String
) extends ASTNode(sl) with AtomicNode
{
}