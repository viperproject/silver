package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation

final class Domain private[silAST](
                                    sl: SourceLocation,
                                    val name: String,
                                    val functions: Set[DomainFunction],
                                    val predicates: Set[DomainPredicate],
                                    val axioms: Set[DomainAxiom]
                                    ) extends ASTNode(sl)
{
  override def toString = "domain " + name + "{" + functions.toString + " " + predicates.toString + " " + axioms.toString + "}"

  override def subNodes = functions.toList ++ predicates.toList ++ axioms.toList
}