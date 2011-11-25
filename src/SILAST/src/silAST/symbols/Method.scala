package silAST.symbols

import silAST.ASTNode

abstract class Method extends ASTNode
{
	val name : String
	val signature : MethodSignature
	val implementations : Set[Implementation]
}