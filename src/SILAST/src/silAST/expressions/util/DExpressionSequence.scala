package silAST.expressions.util

import silAST.expressions.terms.DomainTerm
import silAST.source.SourceLocation

class DExpressionSequence private[silAST](
  sl : SourceLocation,
  override val args: List[DomainTerm]
)
  extends ExpressionSequence(sl, args)
{
  override def asSeq: Seq[DomainTerm] = args
}