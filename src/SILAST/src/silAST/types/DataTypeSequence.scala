package silAST.types

import silAST.ASTNode
import silAST.source.noLocation
import silAST.domains.TypeSubstitution

sealed class DataTypeSequence private[silAST](
                                               val dataTypes: Seq[DataType]
                                               ) extends ASTNode(noLocation) with Seq[DataType]
{
  def isCompatible(other: DataTypeSequence): Boolean =
    dataTypes.length == other.length &&
    dataTypes.zip(other.dataTypes.toSeq).forall((x) => x._1.isCompatible(x._2))
   //covariance

  require(dataTypes.forall(_!=null))
  override def toString = dataTypes.mkString("[", ",", "]")

  override def subNodes = dataTypes

  override def apply(i : Int) = dataTypes(i)
  override def length = dataTypes.length
  override def iterator = dataTypes.iterator

  def substitute(s : TypeSubstitution) = new DataTypeSequence(dataTypes.map(_.substitute(s)))
}

object DataTypeSequence
{
  def apply(dataTypes : DataType*) = new DataTypeSequence(dataTypes)
}
