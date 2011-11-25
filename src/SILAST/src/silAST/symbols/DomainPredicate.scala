package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation

abstract class DomainPredicate(sl : SourceLocation, val name : String) extends ASTNode(sl)
{

}