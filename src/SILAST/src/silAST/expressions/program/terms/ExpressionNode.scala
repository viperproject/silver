package silAST.expressions.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.source.SourceLocation

abstract class ExpressionNode[+T <: TermNode[T]](val sl : SourceLocation) extends ASTNode(sl) {
}