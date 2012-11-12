package semper.sil.ast.symbols.logical.quantification

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation

sealed abstract class Quantifier extends ASTNode
{
  override def comment = List()
}

sealed case class Forall()(override val sourceLocation: SourceLocation) extends Quantifier {
  override def toString: String = "forall"
}

sealed case class Exists()(override val sourceLocation: SourceLocation) extends Quantifier {
  override def toString: String = "exists"
}