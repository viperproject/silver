package semper.sil.ast.symbols.logical

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation

sealed abstract class UnaryConnective private [sil]() extends ASTNode {
  override def toString: String = name

  def name: String
}

final case class Not()(override val sourceLocation: SourceLocation) extends UnaryConnective {

  override val comment = Nil
  def name: String = "!"

}