package silAST.expressions.util

import silAST.expressions.terms.DomainTerm
import silAST.source.SourceLocation

class DArgumentSequence private[silAST](
  sl : SourceLocation,
  override val args: List[DomainTerm]
)
  extends ArgumentSequence(sl, args)
{
  override def asSeq: Seq[DomainTerm] = args
}