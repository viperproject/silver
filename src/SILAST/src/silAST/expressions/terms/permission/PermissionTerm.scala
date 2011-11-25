package silAST.expressions.terms.permission

import silAST.ASTNode
import silAST.AtomicNode

sealed abstract class PermissionTerm extends ASTNode {
}

abstract case class FullPermissionTerm() extends PermissionTerm with AtomicNode
{
}