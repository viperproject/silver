package silAST.symbols.logical.quantification

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.noLocation

sealed abstract class Quantifier extends ASTNode(noLocation) with AtomicNode {
}

abstract case class Forall() extends Quantifier {
  override def toString: String = "forall"
}

abstract case class Exists() extends Quantifier {
  override def toString: String = "exists"
}