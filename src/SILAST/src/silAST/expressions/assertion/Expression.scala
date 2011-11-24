package silAST.expressions.assertion

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.logical.terms.GLogicalTerm

abstract class Expression(sl : SourceLocation) extends ASTNode(sl)
 {
//  type LogicalTerm = GLogicalTerm[LogicalTermTrait]
  def subExpressions : Seq[Expression] 
}