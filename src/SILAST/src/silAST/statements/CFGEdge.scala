package silAST.statements

import silAST.ASTNode
import silAST.expressions.Expression
import silAST.source.SourceLocation

class CFGEdge private[silAST](
  sl : SourceLocation,
  val source: BasicBlock,
  val target: BasicBlock,
  val condition: Expression,
  val isBackEdge: Boolean
) extends ASTNode(sl) {
  override def subNodes = condition :: Nil
}