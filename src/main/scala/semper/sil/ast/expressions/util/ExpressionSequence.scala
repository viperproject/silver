package semper.sil.ast.expressions.util

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.{Expression}
import semper.sil.ast.source.{SourceLocation, noLocation}

/////////////////////////////////////////////////////////////////
sealed class ExpressionSequence private[sil](
                                              val args: Seq[Expression]
                                              ) extends ASTNode with Seq[Expression] {

  override val sourceLocation: SourceLocation = (if (args.isEmpty) noLocation else args.head.sourceLocation)
  override val comment = Nil

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
}
