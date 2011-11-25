package silAST.symbols

import silAST.ASTNode
import silAST.source.SourceLocation

abstract class Implementation extends ASTNode 
{
	val method : Method
	val locals : Set[ProgramVariable]
}