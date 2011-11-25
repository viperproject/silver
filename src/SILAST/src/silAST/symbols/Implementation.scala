package silAST.symbols

import silAST.ASTNode
import silAST.source.SourceLocation

abstract class Implementation( 
		sl : SourceLocation,
		val method : Method,
		val locals : Set[ProgramVariable]
    ) extends ASTNode(sl) 
{
}