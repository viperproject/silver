package silAST.symbols
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.AtomicNode

class ProgramVariable( 
		sl : SourceLocation,
		val name : String, 
		val dataType : DataType
    ) extends ASTNode(sl) with AtomicNode[ProgramVariable]
{
	override def toString() : String = { return name }
}