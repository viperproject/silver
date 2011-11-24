package silAST.expressions

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.symbols.logical.UnaryBooleanOperator
import silAST.ASTNode
import silAST.expressions.terms.GTerm

class UnaryBooleanExpression[+T <: GTerm[T]](
		sl : SourceLocation,
		val operator : UnaryBooleanOperator,
		val expression : GExpression[T]
    )
    extends GExpression[T](sl) {

  override def toString : String = operator.toString + expression.toString
  override def subNodes: Seq[ASTNode] = operator :: (expression :: List.empty[ASTNode])
  override def subExpressions : Seq[GExpression[T]] = expression :: Nil
  

}