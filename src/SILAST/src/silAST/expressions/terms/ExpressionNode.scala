package silAST.expressions.terms

import scala.collection.Seq
import source.SourceLocation
import silAST.ASTNode

abstract class ExpressionNode(val sl : SourceLocation) extends ASTNode(sl) {
}