package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.noLocation

sealed abstract class Quantifier extends ASTNode(noLocation) with AtomicNode

case object Forall extends Quantifier {
  override def toString: String = "forall"
}

case object Exists extends Quantifier {
  override def toString: String = "exists"
}