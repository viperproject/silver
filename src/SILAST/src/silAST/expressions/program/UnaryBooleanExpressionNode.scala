package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.UnaryBooleanOperatorNode
import silAST.ASTNode
import silAST.expressions.terms.GTermNode

class UnaryBooleanExpressionNode[+T <: GTermNode[T]](
		sl : SourceLocation,
		val operator : UnaryBooleanOperatorNode,
		val expression : GProgramExpressionNode[T]
    )
    extends GProgramExpressionNode[T](sl) {

  override def toString : String = { return operator.toString() + expression.toString() }
  override def subNodes(): Seq[ASTNode] = { return operator :: expression :: Nil }
  override def subExpressions(): Seq[GProgramExpressionNode[T]] = { return expression :: Nil }
  

}