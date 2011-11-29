package silAST.expressions.util

import silAST.expressions.terms.ProgramTerm
import silAST.source.SourceLocation

abstract class PArgumentSequence private[silAST](
  sl : SourceLocation,
  override val args: List[ProgramTerm]
) extends ArgumentSequence(sl,args)
{
  override def asSeq: Seq[ProgramTerm] = args
}