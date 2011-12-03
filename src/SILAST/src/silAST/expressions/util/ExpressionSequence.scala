package silAST.expressions.util

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.{GeneralExpression, DomainExpression, ProgramExpression, Expression}

final class GenericExpressionSequence[E <: Expression] private[silAST](
  val sl : SourceLocation,
  val args: Seq[E]
) extends ASTNode(sl) with Seq[E]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
  override val subNodes = args
}

object GenericExpressionSequence{
  type ExpressionSequence = GenericExpressionSequence[Expression]
  type DExpressionSequence = GenericExpressionSequence[DomainExpression]
  type PExpressionSequence = GenericExpressionSequence[ProgramExpression]
  type GExpressionSequence = GenericExpressionSequence[GeneralExpression]
}

