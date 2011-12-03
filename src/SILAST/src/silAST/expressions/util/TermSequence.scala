package silAST.expressions.util

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.terms.{GeneralTerm, ProgramTerm, DomainTerm, Term}

sealed class GenericTermSequence[+T <: Term] private[silAST](
  val sl : SourceLocation,
  val args: Seq[T]
) extends ASTNode(sl) with Seq[T]
{
  override def apply(idx : Int) = args(idx)
  override def iterator = args.iterator
  override val length = args.length
  override val toString = "(" + args.mkString(",") + ")"
  override val subNodes = args
}

object GenericTermSequence{
  type TermSequence = GenericTermSequence[Term]
  type DTermSequence = GenericTermSequence[DomainTerm]
  type PTermSequence = GenericTermSequence[ProgramTerm]
  type GTermSequence = GenericTermSequence[GeneralTerm]
}

