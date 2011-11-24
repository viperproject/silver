package silAST.expressions.assertion.permission

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

sealed abstract class PermissionTerm( sl : SourceLocation ) extends ASTNode(sl) {
}

case class FullPermissionTerm(sl : SourceLocation) extends PermissionTerm(sl)
{
}