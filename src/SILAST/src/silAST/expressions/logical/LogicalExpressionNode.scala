package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class LogicalExpressionNode( sl : SourceLocation) extends PermissionExpressionNode(sl) {

  override def subNodes(): Seq[LogicalExpressionNode];

}