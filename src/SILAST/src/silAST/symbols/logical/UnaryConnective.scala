package silAST.symbols.logical

import silAST.ASTNode
import silAST.source.SourceLocation

sealed abstract class UnaryConnective private[silAST]() extends ASTNode {
  override def toString: String = name

  def name: String
}

final case class Not()(override val sourceLocation: SourceLocation) extends UnaryConnective {

  override val comment = Nil
  def name: String = "!"

}