package silAST.expressions.terms.permission

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.AtomicNode

sealed abstract class PermissionTerm( sl : SourceLocation ) extends ASTNode(sl) {
}

case class FullPermissionTerm(sl : SourceLocation) extends PermissionTerm(sl) with AtomicNode
{
}