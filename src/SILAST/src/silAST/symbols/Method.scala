package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

abstract class Method extends ASTNode
{
	val name : String
	val signature : MethodSignature
	val implementations : Set[Implementation]
}