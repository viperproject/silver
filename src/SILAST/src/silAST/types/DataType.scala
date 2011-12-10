package silAST.types

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}
import silAST.domains.Domain

abstract sealed class DataType(sl: SourceLocation) extends ASTNode(sl) {
  def isCompatible(other : DataType)
}

//final case class ReferenceDataType private[silAST]() extends DataType(noLocation) with AtomicNode {}

object referenceType extends DataType(noLocation) with AtomicNode{
  override val toString = "ref"
  def isCompatible(other : DataType) = other == referenceType
}


final class TypeVariable private[silAST](sl:SourceLocation,domain : Domain, name : String)
  extends ASTNode(sl) with AtomicNode
{
  override val toString = name
}

final case class VariableType(sl:SourceLocation, variable : TypeVariable) extends DataType(sl) with AtomicNode{
  override val toString = variable.toString
  
  def isCompatible(other : DataType) = other match {case VariableType(_,v) => v == variable case _ => false}
}

case class NonReferenceDataType private[silAST](
                                                 sl: SourceLocation,
                                                 val domain: Domain,
                                                 val typeArguments : DataTypeSequence)
  extends DataType(sl) with AtomicNode {
  override val toString = domain.name + (if (typeArguments.length>0) typeArguments.toString else "")

  def isCompatible(other : DataType) =
    other match{
      case NonReferenceDataType(_,d:Domain,ta:DataTypeSequence) => domain == d && typeArguments == ta
      case _ => false
    }
}
