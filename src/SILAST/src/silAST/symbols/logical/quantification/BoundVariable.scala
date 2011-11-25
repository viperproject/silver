package silAST.symbols.logical.quantification
import silAST.ASTNode
import silAST.types.DataType
import silAST.AtomicNode

abstract class BoundVariable extends ASTNode with AtomicNode
{
	val name : String
	val dataType : DataType
	override def toString: String = name

}