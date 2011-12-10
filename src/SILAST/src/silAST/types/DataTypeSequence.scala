package silAST.types

import silAST.ASTNode
import silAST.source.noLocation

sealed class DataTypeSequence private[silAST](
                                               val dataTypes: Seq[DataType]
                                               ) extends ASTNode(noLocation) {
  require(dataTypes.forall(_!=null))
  override def toString = dataTypes.mkString("(", ",", ")")

  override def subNodes = dataTypes
}

object DataTypeSequence
{
  def apply(dataTypes : DataType*) = new DataTypeSequence(dataTypes)
}
