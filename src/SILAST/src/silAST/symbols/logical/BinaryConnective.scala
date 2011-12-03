package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.noLocation

sealed abstract class BinaryConnective extends ASTNode(noLocation) {

  override def toString: String = {
    name
  }

  override def subNodes: Seq[ASTNode] = {
    Nil
  }

  def name: String

}

abstract case class EquivalenceOperatorNode() extends BinaryConnective {
  def name: String = {
    "<==>"
  }
}

abstract case class ImplicationOperator() extends BinaryConnective {
  def name: String = {
    "==>"
  }
}

abstract case class OrOperator() extends BinaryConnective {
  def name: String = {
    "||"
  }
}

abstract case class AndOperator() extends BinaryConnective {
  def name: String = {
    "&&"
  }
}
