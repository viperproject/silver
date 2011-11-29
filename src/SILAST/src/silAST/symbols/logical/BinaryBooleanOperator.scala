package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.{noLocation, SourceLocation}

sealed abstract class BinaryBooleanOperator extends ASTNode(noLocation) {

  override def toString: String = {
    name
  }

  override def subNodes: Seq[ASTNode] = {
    Nil
  }

  def name: String

}

abstract case class EquivalenceOperatorNode() extends BinaryBooleanOperator {
  def name: String = {
    "<==>"
  }
}

abstract case class ImplicationOperator() extends BinaryBooleanOperator {
  def name: String = {
    "==>"
  }
}

abstract case class OrOperator() extends BinaryBooleanOperator {
  def name: String = {
    "||"
  }
}

abstract case class AndOperator() extends BinaryBooleanOperator {
  def name: String = {
    "&&"
  }
}
