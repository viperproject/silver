package silAST.types

import silAST.ASTNode
import silAST.source.{noLocation, SourceLocation}
import silAST.domains.{DomainTemplate, DomainTemplateInstance, TypeSubstitution, Domain}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
sealed abstract class DataType(sl:SourceLocation) extends ASTNode(sl)
{
  def isCompatible(other : DataType) : Boolean

  def substitute(s : TypeSubstitution) : DataType = this
  
  def freeTypeVariables : collection.Set[TypeVariable] = Set()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
object referenceType extends DataType(noLocation)
{
  override val toString = "ref"
  def isCompatible(other : DataType) = other == referenceType
}


/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
final class TypeVariable private[silAST](sl:SourceLocation,template : DomainTemplate, val name : String)
  extends ASTNode(sl)
{
  override val toString = name
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
final case class VariableType(sl:SourceLocation, variable : TypeVariable) extends DataType(sl)
{
  override val toString = variable.name
  
  override def isCompatible(other : DataType) =
    other match {case VariableType(_,v) => v == variable case _ => false}

  override def substitute(s : TypeSubstitution) = s.mapType(variable,this)
  override def freeTypeVariables = Set(variable)
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
case class NonReferenceDataType private[silAST](
                                                 sl: SourceLocation,
                                                 domain: Domain
                                                 )
  extends DataType(sl)
{
  override def freeTypeVariables = domain.freeTypeVariables

  override val toString = domain.name

  def isCompatible(other : DataType) =
    other match{
      case NonReferenceDataType(_,d:DomainTemplateInstance) => domain.isCompatible(other)
      case _ => false
    }

  override def substitute(s:TypeSubstitution) =
    if (s.typeVariables.intersect(freeTypeVariables).isEmpty)
      this
    else
      new NonReferenceDataType(s.sourceLocation, domain.getInstance(s))
}
