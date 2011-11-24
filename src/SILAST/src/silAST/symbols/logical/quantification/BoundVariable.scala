package silAST.symbols.logical.quantification
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.symbols.DataType
import silAST.AtomicNode

class BoundVariable( 
		sl : SourceLocation,
		val name : String, 
		val dataType : DataType
	) extends ASTNode(sl) with AtomicNode
{
	override def toString() : String = { return name }

}