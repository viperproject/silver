package silAST.symbols

import silAST.ASTNode

abstract class Implementation extends ASTNode
{
	val method : Method
	val locals : Set[ProgramVariable]
}