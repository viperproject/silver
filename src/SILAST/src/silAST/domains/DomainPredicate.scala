package silAST.domains
import silAST.ASTNode
import silAST.source.SourceLocation

abstract class DomainPredicate extends ASTNode
{
	val name : String
}