package silAST.statements

import silAST.ASTNode
import silAST.expressions.Expression

abstract class CFGEdge extends ASTNode {
  val source: BasicBlock
  val target: BasicBlock
  val condition: Expression
  val isBackEdge: Boolean
}