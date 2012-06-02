package silAST.methods.implementations

import silAST.ASTNode
import silAST.expressions.Expression
import silAST.source.SourceLocation

final class CFGEdge private[silAST]
(

  val source: Block,
  val target: Block,
  val condition: Expression
  )(val sourceLocation: SourceLocation,val comment:List[String])
  extends ASTNode {
  require(source.cfg == target.cfg)
  target.addPredecessor(this)

  //////////////////////////////////////////////////////////////////////////////
  override def toString = source.label + " ==> " + "[" + condition.toString + "]" + target.label.toString

  override def equals(other: Any): Boolean = {
    other match {
      case e: CFGEdge => e eq this
      case _ => false
    }
  }

  override def hashCode(): Int = source.hashCode() + target.hashCode() + condition.hashCode()
}