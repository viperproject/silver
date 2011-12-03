package silAST.expressions.util

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.{GeneralTerm, ProgramTerm, DomainTerm, Term}

sealed class TermSequence private[silAST](
  val sl : SourceLocation,
  val args: Seq[Term]
) extends ASTNode(sl) with Seq[Term]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
  override val subNodes = args
}

///////////////////////////////////////////////////////////////
sealed trait PTermSequence extends TermSequence with Seq[ProgramTerm]
{
  override val args : Seq[ProgramTerm] = pArgs
  protected val pArgs : Seq[ProgramTerm]
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
}

private[silAST] final class PTermSequenceC(
  sl : SourceLocation,
  args : Seq[ProgramTerm]
) extends TermSequence(sl,args) with PTermSequence{
  override val pArgs = args
}

///////////////////////////////////////////////////////////////
sealed trait DTermSequence extends TermSequence with Seq[DomainTerm]
{
  override val args: Seq[DomainTerm] = dArgs
  protected val dArgs : Seq[DomainTerm]
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
}

private[silAST] final class DTermSequenceC(
  sl : SourceLocation,
  args : Seq[DomainTerm]
) extends TermSequence(sl,args) with DTermSequence{
  override val dArgs = args
}


///////////////////////////////////////////////////////////////
final class GTermSequence private[silAST](
  sl : SourceLocation,
  override val args: Seq[GeneralTerm]
) extends TermSequence(sl,args) with DTermSequence with PTermSequence with Seq[GeneralTerm]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override val dArgs = args
  override val pArgs = args
}

