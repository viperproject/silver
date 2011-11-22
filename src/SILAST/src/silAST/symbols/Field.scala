package silAST.symbols
import silAST.ASTNode
import silAST.source.SourceLocation
import silAST.AtomicNode

class Field( sl : SourceLocation, val name : String, val dataType : DataType) extends ASTNode(sl) with AtomicNode[Field]{
	override def toString() : String = {return name}
}