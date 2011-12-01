package silAST.expressions.util

import silAST.expressions.terms.DomainTerm
import silAST.source.SourceLocation

class DTermSequence private[silAST](
  sl : SourceLocation,
  override val args: List[DomainTerm]
)
  extends TermSequence(sl, args)
{
  override def asSeq: Seq[DomainTerm] = args
}