package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode
import silAST.symbols.logical.UnaryBooleanOperatorNode
import silAST.ASTNode

class UnaryBooleanExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		val operator : UnaryBooleanOperatorNode,
		val expression : ProgramExpressionNode[T]
    )
    extends ProgramExpressionNode[T](sl) {

  override def toString : String = { return operator.toString() + expression.toString() }
  override def subNodes(): Seq[ASTNode] = { return operator :: expression :: Nil }
  override def subExpressions(): Seq[ProgramExpressionNode[T]] = { return expression :: Nil }
  

}