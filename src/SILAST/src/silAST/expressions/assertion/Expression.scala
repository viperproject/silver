package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class Expression(sl : SourceLocation) extends ASTNode(sl)
 {
  def subExpressions : Seq[Expression] 
}