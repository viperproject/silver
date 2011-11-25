package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation

abstract class Predicate(sl : SourceLocation, val name : String) extends ASTNode(sl)
{

}