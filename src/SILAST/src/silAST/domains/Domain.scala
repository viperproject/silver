package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import collection.Set
import collection.mutable.HashSet

final class Domain private[silAST](
                                    sl: SourceLocation,
                                    val name: String
                                    ) extends ASTNode(sl)
{
  private[silAST] val pFunctions = new HashSet[DomainFunction]
  private[silAST] val pPredicates =new HashSet[DomainPredicate]
  private[silAST] val pAxioms = new HashSet[DomainAxiom]

  val functions : Set[DomainFunction] = pFunctions
  val predicates : Set[DomainPredicate] = pPredicates
  val axioms : Set[DomainAxiom] = pAxioms


  override def toString = "domain " + name + "{" + functions.toString + " " + predicates.toString + " " + axioms.toString + "}"

  override def subNodes = functions.toList ++ predicates.toList ++ axioms.toList
}