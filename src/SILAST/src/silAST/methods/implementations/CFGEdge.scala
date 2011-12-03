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
  override def toString = source.label + " ==> " + target.label.toString //TODO condition
  override def subNodes = condition :: Nil
}