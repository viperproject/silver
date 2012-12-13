package semper.sil.ast.symbols.logical

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation

sealed abstract class BinaryConnective extends ASTNode {

  override def toString = name

  override def comment = List()

  def name: String

}

final case class Equivalence()(override val sourceLocation: SourceLocation) extends BinaryConnective {
  def name: String = {
    "<==>"
  }
}

final case class Implication()(override val sourceLocation: SourceLocation) extends BinaryConnective {
  def name: String = {
    "==>"
  }
}

final case class Or()(override val sourceLocation: SourceLocation) extends BinaryConnective {
  def name: String = {
    "||"
  }
}

final case class And()(override val sourceLocation: SourceLocation) extends BinaryConnective {
  def name: String = {
    "&&"
  }
}
