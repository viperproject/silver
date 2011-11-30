package silAST.expressions.util

import silAST.expressions.terms.ProgramTerm
import silAST.source.SourceLocation

final class PExpressionSequence private[silAST](
  sl : SourceLocation,
  override val args: List[ProgramTerm]
) extends ExpressionSequence(sl,args)
{
  override def asSeq: Seq[ProgramTerm] = args
}