package silAST.symbols
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class Function(sl : SourceLocation, val name : String) extends ASTNode(sl)
{

}