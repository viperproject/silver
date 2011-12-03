package silAST.expressions.util

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.{GeneralExpression, DomainExpression, ProgramExpression, Expression}

/////////////////////////////////////////////////////////////////
sealed class ExpressionSequence private[silAST](
  val sl : SourceLocation,
  val args: Seq[Expression]
) extends ASTNode(sl) with Seq[Expression]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
  override val subNodes = args
}

/////////////////////////////////////////////////////////////////
sealed trait PExpressionSequence extends ExpressionSequence with Seq[ProgramExpression]
{
  override val args : Seq[ProgramExpression] = pArgs
  protected val pArgs : Seq[ProgramExpression]
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
}

/////////////////////////////////////////////////////////////////
private final class PExpressionSequenceC private[silAST](
  sl : SourceLocation,
  args: Seq[ProgramExpression]
) extends ExpressionSequence(sl,args) with PExpressionSequence
{
  override val pArgs = args
}


/////////////////////////////////////////////////////////////////
sealed trait DExpressionSequence extends ExpressionSequence with Seq[DomainExpression]
{
  override val args : Seq[DomainExpression] = dArgs
  protected val dArgs : Seq[DomainExpression]
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
}

/////////////////////////////////////////////////////////////////
private final class DExpressionSequenceC private[silAST](
  sl : SourceLocation,
  args: Seq[DomainExpression]
) extends ExpressionSequence(sl,args) with DExpressionSequence
{
  override val dArgs = args
}

/////////////////////////////////////////////////////////////////
final class GExpressionSequence private[silAST](
  sl : SourceLocation,
  override val args: Seq[GeneralExpression]
) extends ExpressionSequence(sl,args) with PExpressionSequence with DExpressionSequence with Seq[GeneralExpression]
{
  override val pArgs = args
  override val dArgs = args
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
}

