package silAST.expressions.terms.permission

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}

sealed abstract class PermissionTerm protected[silAST](sl : SourceLocation) extends ASTNode(sl)
{
}

case class FullPermissionTerm private[silAST]() extends PermissionTerm(noLocation) with AtomicNode
{
}