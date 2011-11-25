package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.types.DataType

abstract class DataTypeSequence(
		sl : SourceLocation,
		val dataTypes : Seq[DataType]
    )
    extends ASTNode(sl) 
{
}