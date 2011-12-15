package silAST.expressions.util

import silAST.ASTNode
import silAST.expressions.{GExpression, DExpression, PExpression, Expression}
import silAST.source.noLocation

/////////////////////////////////////////////////////////////////
sealed class ExpressionSequence private[silAST](
                                                 //                                                 val sl: SourceLocation,
                                                 val args: Seq[Expression]
                                                 ) extends ASTNode(if (args.isEmpty) noLocation else args.head.sourceLocation) with Seq[Expression] {

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
}

/////////////////////////////////////////////////////////////////
sealed trait PExpressionSequence extends ExpressionSequence with Seq[PExpression] {
  override val args: Seq[PExpression] = pArgs

  protected def pArgs: Seq[PExpression]

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator
}

/////////////////////////////////////////////////////////////////
private final class PExpressionSequenceC private[silAST](
                                                          //                                                          sl: SourceLocation,
                                                          args: Seq[PExpression]
                                                          ) extends ExpressionSequence(args) with PExpressionSequence {
  override val pArgs = args
}


/////////////////////////////////////////////////////////////////
sealed trait DExpressionSequence extends ExpressionSequence with Seq[DExpression] {
  override val args: Seq[DExpression] = dArgs

  protected def dArgs: Seq[DExpression]

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator
}

/////////////////////////////////////////////////////////////////
private final class DExpressionSequenceC private[silAST](
                                                          //                                                          sl: SourceLocation,
                                                          args: Seq[DExpression]
                                                          ) extends ExpressionSequence(args) with DExpressionSequence {
  override val dArgs = args
}

/////////////////////////////////////////////////////////////////
final class GExpressionSequence private[silAST](
                                                 //                                                 sl: SourceLocation,
                                                 override val args: Seq[GExpression]
                                                 ) extends ExpressionSequence(args) with PExpressionSequence with DExpressionSequence with Seq[GExpression] {
  override val pArgs = args
  override val dArgs = args

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator
}

