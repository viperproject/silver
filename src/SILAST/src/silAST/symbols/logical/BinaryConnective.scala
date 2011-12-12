package silAST.symbols.logical

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.noLocation

sealed abstract class BinaryConnective extends ASTNode(noLocation) {

  override def toString = name

  def name: String

}

final case class Equivalence() extends BinaryConnective {
  def name: String = {
    "<==>"
  }
}

final case class Implication() extends BinaryConnective {
  def name: String = {
    "==>"
  }
}

final case class Or() extends BinaryConnective {
  def name: String = {
    "||"
  }
}

final case class And() extends BinaryConnective {
  def name: String = {
    "&&"
  }
}
