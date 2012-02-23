package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.source.{SourceLocation, noLocation}

sealed abstract class Quantifier extends ASTNode

sealed case class Forall()(override val sourceLocation : SourceLocation) extends Quantifier {
  override def toString: String = "forall"
}

sealed case class Exists()(override val sourceLocation : SourceLocation) extends Quantifier {
  override def toString: String = "exists"
}