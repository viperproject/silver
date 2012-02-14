package silAST.symbols.logical

import silAST.ASTNode
import silAST.source.{SourceLocation, noLocation}

sealed abstract class BinaryConnective extends ASTNode {

  override def toString = name

  def name: String

}

final case class Equivalence(sourceLocation : SourceLocation) extends BinaryConnective {
  def name: String = {
    "<==>"
  }
}

final case class Implication(sourceLocation : SourceLocation) extends BinaryConnective {
  def name: String = {
    "==>"
  }
}

final case class Or(sourceLocation : SourceLocation) extends BinaryConnective {
  def name: String = {
    "||"
  }
}

final case class And(sourceLocation : SourceLocation) extends BinaryConnective {
  def name: String = {
    "&&"
  }
}
