package silAST.expressions.terms.permission

import silAST.source.SourceLocation
import silAST.{AtomicNode, ASTNode}


final class PermissionVariable private[silAST](sl : SourceLocation, val name : String)
  extends ASTNode(sl) with AtomicNode
{
  override val toString = name
}