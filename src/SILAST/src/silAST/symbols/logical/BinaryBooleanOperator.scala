package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

sealed abstract class BinaryBooleanOperator(sl : SourceLocation) extends ASTNode(sl) {

  override def toString : String = { return name }
  override def subNodes(): Seq[ASTNode] = { Nil }

  def name : String

}

case class EquivalenceOperatorNode(sl:SourceLocation) extends BinaryBooleanOperator(sl) {
  def name : String = { return "<==>" }
}

case class ImplicationOperator(sl:SourceLocation) extends BinaryBooleanOperator(sl) {
  def name : String = { return "==>" }
}

case class OrOperator(sl:SourceLocation) extends BinaryBooleanOperator(sl) {
  def name : String = { return "||" }
}

case class AndOperator(sl:SourceLocation) extends BinaryBooleanOperator(sl) {

  def name : String = { return "&&" }

}