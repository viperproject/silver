package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.source.{SourceLocation, noLocation}

sealed abstract class Quantifier extends ASTNode

sealed case class Forall(sourceLocation : SourceLocation) extends Quantifier {
  override def toString: String = "forall"
}

sealed case class Exists(sourceLocation : SourceLocation) extends Quantifier {
  override def toString: String = "exists"
}