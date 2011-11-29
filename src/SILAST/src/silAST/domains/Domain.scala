package silAST.domains

import silAST.ASTNode

abstract class Domain extends ASTNode {
  val name: String
  val functions: Set[DomainFunction]
  val predicates: Set[DomainPredicate]
  val axioms: Set[DomainAxiom]
}