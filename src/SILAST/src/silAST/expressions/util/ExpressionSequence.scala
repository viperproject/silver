package silAST.expressions.util

import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.source.SourceLocation

class ExpressionSequence protected[silAST](
  sl : SourceLocation,
  val args: List[Term]
) extends ASTNode(sl) {

  def asSeq: Seq[Term] = args

  override def toString = "(" + args.mkString(",") + ")"
  override def subNodes = args
}
//TODO: parameter sequence