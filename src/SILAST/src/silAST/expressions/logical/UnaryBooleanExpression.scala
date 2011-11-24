package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.UnaryBooleanOperator
import silAST.ASTNode
import silAST.expressions.logical.terms.GLogicalTerm

class UnaryBooleanExpression[+T <: GLogicalTerm[T]](
		sl : SourceLocation,
		val operator : UnaryBooleanOperator,
		val expression : GProgramExpression[T]
    )
    extends GProgramExpression[T](sl) {

  override def toString : String = { return operator.toString() + expression.toString() }
  override def subNodes(): Seq[ASTNode] = { return operator :: (expression :: List.empty[ASTNode]) }
  override def subExpressions(): Seq[GProgramExpression[T]] = { return expression :: Nil }
  

}