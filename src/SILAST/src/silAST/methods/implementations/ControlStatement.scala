package silAST.methods.implementations

import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.symbols.logical.Not
import silAST.expressions.{TrueExpression, PExpression}

sealed abstract class ControlStatement
  extends ASTNode {
  def successors: Set[CFGEdge]
}


final class Halt()(val sourceLocation: SourceLocation) extends ControlStatement {
  override val successors: Set[CFGEdge] = Set()

  override val toString = "Halt"

  override def equals(other: Any) = other match {
    case h: Halt => true
    case _ => false
  }

  override val hashCode = toString.hashCode()
}

final class Branch private[silAST]
(

  val source: Block,
  val trueTarget: Block,
  val falseTarget: Block,
  val condition: PExpression
  )(val sourceLocation: SourceLocation)
  extends ControlStatement {
  require(source.cfg == trueTarget.cfg)
  require(source.cfg == falseTarget.cfg)
  private val conditionNegation = source.factory.scope.factory.makeUnaryExpression(new Not()(sourceLocation), condition)(sourceLocation)

  private val trueEdge = new CFGEdge(source, trueTarget, condition)(sourceLocation)
  private val falseEdge = new CFGEdge(source, falseTarget, conditionNegation)(sourceLocation)
  override val successors: Set[CFGEdge] = Set(trueEdge, falseEdge)

  override val toString = "if " + condition.toString + " then goto " + trueTarget.label + " else goto " + falseTarget.label

  override def equals(other: Any) = other match {
    case b: Branch => b eq this
    case _ => false
  }

  override val hashCode = toString.hashCode()

}

final class Goto private[silAST]
(
  val source: Block,
  val target: Block
  )
(val sourceLocation: SourceLocation)
  extends ControlStatement {
  require(source.cfg == target.cfg)

  private val edge = new CFGEdge(source, target, TrueExpression()(sourceLocation))(sourceLocation)
  override val successors: Set[CFGEdge] = Set(edge)

  override val toString = "goto " + target.label

  override def equals(other: Any) = other match {
    case g: Goto => g eq this
    case _ => false
  }

  override val hashCode = toString.hashCode()

}
