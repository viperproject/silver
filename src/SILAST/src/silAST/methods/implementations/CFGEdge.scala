package silAST.methods.implementations

import silAST.ASTNode
import silAST.expressions.Expression
import silAST.source.SourceLocation

final class CFGEdge private[silAST](
                                     sl: SourceLocation,
                                     val source: BasicBlock,
                                     val target: BasicBlock,
                                     val condition: Expression,
                                     val isBackEdge: Boolean
                                     ) extends ASTNode(sl) {
  require(source.cfg == target.cfg)
  source.addSuccessor(this)
  target.addPredecessor(this)

  override def toString = source.label + " ==> "  + "[" + condition.toString + "]" + target.label.toString
  override def subNodes = condition :: Nil
}