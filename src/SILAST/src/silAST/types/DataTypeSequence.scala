package silAST.types

import silAST.ASTNode
import silAST.source.noLocation

sealed class DataTypeSequence private[silAST](
                                               val dataTypes: Seq[DataType]
                                               ) extends ASTNode(noLocation) with Seq[DataType]
{
  require(dataTypes.forall(_!=null))
  override def toString = dataTypes.mkString("[", ",", "]")

  override def subNodes = dataTypes

  override def apply(i : Int) = dataTypes(i)
  override def length = dataTypes.length
  override def iterator = dataTypes.iterator
}

object DataTypeSequence
{
  def apply(dataTypes : DataType*) = new DataTypeSequence(dataTypes)
}
