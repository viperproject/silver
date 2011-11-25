package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.Expression

abstract class MethodSignature extends ASTNode
{
	val arguments : Seq[ProgramVariable]
	val result : ProgramVariable
	val precondition  : Seq[Expression]
	val postcondition : Seq[Expression]
}