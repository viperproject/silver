package silAST.domains

import silAST.ASTNode
import silAST.expressions.DomainExpression
import silAST.source.SourceLocation

final class DomainAxiom private[silAST](
                                         sl: SourceLocation,
                                         val name: String,
                                         val expression: DomainExpression
                                         ) extends ASTNode(sl) {
  override def toString = "axiom " + name + " = " + expression.toString

  override def subNodes = expression :: Nil
}