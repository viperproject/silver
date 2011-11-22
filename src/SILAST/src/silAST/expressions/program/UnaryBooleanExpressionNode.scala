package silAST.expressions.program

import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.terms.TermNode

abstract class UnaryBooleanExpressionNode[+T <: TermNode[T]](
		sl : SourceLocation,
		val expression : ProgramExpressionNode[T]
    )
    extends ProgramExpressionNode[T](sl) {

  override def subNodes(): Seq[ProgramExpressionNode[T]] = { return expression :: Nil }

}