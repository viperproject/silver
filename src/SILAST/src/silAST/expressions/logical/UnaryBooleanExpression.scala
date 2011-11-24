package silAST.expressions.logical

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.UnaryBooleanOperator
import silAST.ASTNode
import silAST.expressions.assertion.terms.GTerm

class UnaryBooleanExpression[+T <: GTerm[T]](
		sl : SourceLocation,
		val operator : UnaryBooleanOperator,
		val expression : GLogicalExpression[T]
    )
    extends GLogicalExpression[T](sl) {

  override def toString : String = operator.toString + expression.toString
  override def subNodes: Seq[ASTNode] = operator :: (expression :: List.empty[ASTNode])
  override def subExpressions : Seq[GLogicalExpression[T]] = expression :: Nil
  

}