package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.types.DataType
import silAST.source.SourceLocation

final class DataTypeSequence private[silAST](
  sl : SourceLocation,
  val dataTypes: Seq[DataType]
) extends ASTNode(sl)
{
  override def toString = dataTypes.toString
  override def subNodes = dataTypes
}