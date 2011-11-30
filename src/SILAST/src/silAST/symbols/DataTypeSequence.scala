package silAST.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.types.DataType
import silAST.source.{noLocation, SourceLocation}

final class DataTypeSequence private[silAST](
  val dataTypes: List[DataType]
) extends ASTNode(noLocation)
{
  override def toString = dataTypes.mkString ("(",",",")")
  override def subNodes = dataTypes
}