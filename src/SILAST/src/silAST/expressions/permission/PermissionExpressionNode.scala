package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class PermissionExpressionNode(sl : SourceLocation) extends ASTNode(sl) {

  override def subNodes(): Seq[PermissionExpressionNode];

}