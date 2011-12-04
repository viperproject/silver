package silAST.expressions.util

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.{GTerm, PTerm, DTerm, Term}

sealed class TermSequence private[silAST](
                                           val sl: SourceLocation,
                                           val args: Seq[Term]
                                           ) extends ASTNode(sl) with Seq[Term] {
  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
  override val subNodes = args
}

///////////////////////////////////////////////////////////////
sealed trait PTermSequence extends TermSequence with Seq[PTerm] {
  override val args: Seq[PTerm] = pArgs
  protected val pArgs: Seq[PTerm]

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator
}

private[silAST] final class PTermSequenceC(
                                            sl: SourceLocation,
                                            args: Seq[PTerm]
                                            ) extends TermSequence(sl, args) with PTermSequence {
  override val pArgs = args
}

///////////////////////////////////////////////////////////////
sealed trait DTermSequence extends TermSequence with Seq[DTerm] {
  override val args: Seq[DTerm] = dArgs
  protected def dArgs: Seq[DTerm]

  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator
}

private[silAST] final class DTermSequenceC(
                                            sl: SourceLocation,
                                            args: Seq[DTerm]
                                            ) extends TermSequence(sl, args) with DTermSequence {
  override def dArgs = args
}


///////////////////////////////////////////////////////////////
final class GTermSequence private[silAST](
                                           sl: SourceLocation,
                                           override val args: Seq[GTerm]
                                           ) extends TermSequence(sl, args) with DTermSequence with PTermSequence with Seq[GTerm] {
  override def apply(idx: Int) = args(idx)

  override def iterator = args.iterator

  override val dArgs = args
  override val pArgs = args
}

