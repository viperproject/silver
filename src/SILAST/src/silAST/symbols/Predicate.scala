package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.expressions.Expression

abstract class Predicate extends ASTNode
{
	val name : String
	val expression : Expression
}