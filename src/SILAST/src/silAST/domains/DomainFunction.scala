package silAST.domains
import silAST.ASTNode
import silAST.source.SourceLocation

abstract class DomainFunction() extends ASTNode
{
	val name : String
}