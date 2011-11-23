package silAST.symbols
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.AtomicNode

class ProgramVariable( 
		sl : SourceLocation,
		val name : String, 
		val dataType : DataType
    ) extends ASTNode(sl)
{
	override def toString : String = { return name }
	override def subNodes : Seq[ASTNode] = { return dataType :: Nil }
}