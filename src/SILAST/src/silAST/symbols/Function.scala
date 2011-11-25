package silAST.symbols
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class Function extends ASTNode
{
	val name : String
	val signature : FunctionSignature
}