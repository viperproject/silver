package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.types.DataType
import silAST.source.SourceLocation

class DataTypeSequence(
                sl : SourceLocation,
                val dataTypes: Seq[DataType]
           ) extends ASTNode(sl)
{

}