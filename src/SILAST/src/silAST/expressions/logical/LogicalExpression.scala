package silAST.expressions.logical

import silAST.ASTNode
import scala.collection.Seq
import source.SourceLocation

abstract class LogicalExpression(sl:SourceLocation) extends ASTNode(sl) {

  def subNodes(): Seq[LogicalExpression];

}