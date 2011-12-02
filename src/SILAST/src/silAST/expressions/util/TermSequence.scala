package silAST.expressions.util

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.{ProgramTerm, DomainTerm, Term}

sealed class TermSequence protected[silAST](
  sl : SourceLocation,
  val args: Seq[Term]
) extends ASTNode(sl) with Seq[Term]
{
//  def asSeq: Seq[T] = args

  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override def length = args.length
  override def toString = "(" + args.mkString(",") + ")"
  override def subNodes = args
}

final class DTermSequence protected[silAST](
  sl : SourceLocation,
  override val args: Seq[DomainTerm]
) extends TermSequence(sl,args) with Seq[DomainTerm]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override def toString = "(" + args.mkString(",") + ")"
  override def subNodes = args
}

final class PTermSequence protected[silAST](
  sl : SourceLocation,
  override val args: Seq[ProgramTerm]
) extends TermSequence(sl,args) with Seq[ProgramTerm]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override def toString = "(" + args.mkString(",") + ")"
  override def subNodes = args
}
