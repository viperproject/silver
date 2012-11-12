package semper.sil.ast.expressions.util

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.{GExpression, DExpression, PExpression, Expression}
import semper.sil.ast.source.{SourceLocation, noLocation}

/////////////////////////////////////////////////////////////////
sealed class ExpressionSequence private [sil](
                                                 val args: Seq[Expression]
                                                 ) extends ASTNode with Seq[Expression] {

  override val sourceLocation: SourceLocation = (if (args.isEmpty) noLocation else args.head.sourceLocation)
  override val comment = Nil

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
private final class PExpressionSequenceC private [sil](
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
private final class DExpressionSequenceC private [sil](
                                                          args: Seq[DExpression]
                                                          ) extends ExpressionSequence(args) with DExpressionSequence {
  override val dArgs = args
}

/////////////////////////////////////////////////////////////////
final class GExpressionSequence private [sil](
                                                 override val args: Seq[GExpression]
                                                 ) extends ExpressionSequence(args) with PExpressionSequence with DExpressionSequence with Seq[GExpression] {
  override val pArgs = args
  override val dArgs = args

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator
}

