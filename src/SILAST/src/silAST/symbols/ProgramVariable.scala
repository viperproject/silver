package silAST.symbols
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.AtomicNode
import silAST.types.DataType

abstract class ProgramVariable extends ASTNode
{
	val name : String
	val dataType : DataType
	override def toString : String = name
	override def subNodes : Seq[ASTNode] = dataType :: Nil
}