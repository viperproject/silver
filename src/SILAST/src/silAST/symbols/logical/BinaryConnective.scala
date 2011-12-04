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

final case class EquivalenceOperatorNode() extends BinaryConnective { //TODO: singletons
  def name: String = {
    "<==>"
  }
}

final case class ImplicationOperator() extends BinaryConnective {
  def name: String = {
    "==>"
  }
}

final case class OrOperator() extends BinaryConnective {
  def name: String = {
    "||"
  }
}

final case class AndOperator() extends BinaryConnective {
  def name: String = {
    "&&"
  }
}
