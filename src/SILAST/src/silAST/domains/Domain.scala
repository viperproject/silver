package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation

class Domain private[silAST](
  sl : SourceLocation,
  val name: String,
  val functions: Set[DomainFunction],
  val predicates: Set[DomainPredicate],
  val axioms: Set[DomainAxiom]
) extends ASTNode(sl)
{
}