package silAST.domains

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class Domain extends ASTNode 
{
	val name : String
	val functions : Set[DomainFunction]
	val predicates : Set[DomainPredicate]
	val axioms : Set[DomainAxiom]
}