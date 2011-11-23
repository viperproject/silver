package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.UnaryBooleanOperatorNode
import silAST.ASTNode
import silAST.expressions.terms.GTerm

class UnaryBooleanExpressionNode[+T <: GTerm[T]](
		sl : SourceLocation,
		val operator : UnaryBooleanOperatorNode,
		val expression : GProgramExpression[T]
    )
    extends GProgramExpression[T](sl) {

  override def toString : String = { return operator.toString() + expression.toString() }
  override def subNodes(): Seq[ASTNode] = { return operator :: (expression :: List.empty[ASTNode]) }
  override def subExpressions(): Seq[GProgramExpression[T]] = { return expression :: Nil }
  

}