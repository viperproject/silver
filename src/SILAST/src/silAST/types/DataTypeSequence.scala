package silAST.types

import silAST.ASTNode
import silAST.domains.TypeVariableSubstitution
import silAST.source.{SourceLocation, noLocation}

sealed class DataTypeSequence private[silAST](
                                               val dataTypes: Seq[DataType]
                                               ) extends ASTNode with Seq[DataType]
{
  def freeTypeVariables = (for (t<-dataTypes) yield t.freeTypeVariables).flatten

  override val sourceLocation : SourceLocation = if (dataTypes.isEmpty) noLocation else dataTypes.head.sourceLocation

  def isCompatible(other: DataTypeSequence): Boolean =
    dataTypes.length == other.length &&
    dataTypes.zip(other.dataTypes.toSeq).forall((x) => x._1.isCompatible(x._2))
   //covariance

  require(dataTypes.forall(_!=null))
  override def toString() = dataTypes.mkString("[", ",", "]")

  override def apply(i : Int) = dataTypes(i)
  override def length = dataTypes.length
  override def iterator = dataTypes.iterator

  def substitute(s : TypeVariableSubstitution) = new DataTypeSequence(dataTypes.map(_.substitute(s)))

  override def equals(other : Any) = {
    other match{
      case dts : DataTypeSequence => dataTypes == dts.dataTypes
      case _ => false
    }
  }
  
  override def hashCode() : Int = if (dataTypes.isEmpty) 0 else dataTypes.foldLeft(0)((x,y)=>(x+y.hashCode()))
}

object DataTypeSequence
{
  def apply(dataTypes : DataType*) = new DataTypeSequence(dataTypes)
}
