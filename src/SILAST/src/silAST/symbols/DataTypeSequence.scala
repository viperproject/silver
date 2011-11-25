package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.types.DataType

abstract class DataTypeSequence extends ASTNode
{
	val dataTypes : Seq[DataType]
}