package silAST.types

import silAST.ASTNode
import silAST.source.{noLocation, SourceLocation}
import silAST.domains.{TypeVariableSubstitution, Domain}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
sealed abstract class DataType extends ASTNode
{
  def isCompatible(other : DataType) : Boolean

  def substitute(s : TypeVariableSubstitution) : DataType = this
  
  def freeTypeVariables : collection.Set[TypeVariable] = Set()

  def domain : Domain
  
  override def equals(other : Any) : Boolean
  override def hashCode() : Int
}



/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
final class TypeVariable private[silAST](val name : String, val domain : Domain)(val sourceLocation : SourceLocation)
  extends ASTNode
{
  override val toString = name

  override def equals(other : Any) : Boolean = 
  {
    other match{
      case v : TypeVariable => this eq  v
      case _ => false
    }
  }
  override def hashCode() : Int = name.hashCode()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
final case class VariableType(

                               variable : TypeVariable
                             )(override val sourceLocation:SourceLocation) extends DataType
{
  override val toString = variable.name
  
  override def isCompatible(other : DataType) =
    other match {case VariableType(v) => v == variable case _ => false}

  override def substitute(s : TypeVariableSubstitution) = s.mapType(variable,this)
  override def freeTypeVariables = Set(variable)

  override val domain = variable.domain

  override def equals(other : Any) : Boolean =
  {
    other match{
      case v : VariableType => variable == v.variable
      case _ => false
    }
  }
  override def hashCode() : Int = variable.hashCode()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
case class NonReferenceDataType private[silAST](

                                                 domain: Domain
                                                 )(override val sourceLocation : SourceLocation)
  extends DataType
{
  require (domain ne  referenceDomain)

  override def freeTypeVariables = domain.freeTypeVariables

  override val toString = domain.fullName

  def isCompatible(other : DataType) =
    other match{
      case NonReferenceDataType(d) => domain.isCompatible(d)
      case _ => false
    }

  override def substitute(s:TypeVariableSubstitution) =   {
    if (s.typeVariables.intersect(freeTypeVariables).isEmpty)
      this
    else
      new NonReferenceDataType(domain.substitute(s))(s.sourceLocation)
  }

  override def equals(other : Any) : Boolean =
  {
    other match{
      case t : NonReferenceDataType => domain == t.domain
      case _ => false
    }
  }
  override def hashCode() : Int = domain.fullName.hashCode()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
case class ReferenceDataType private[silAST] () extends DataType
{
  override val sourceLocation = noLocation
  val domain = referenceDomain
  override def freeTypeVariables = domain.freeTypeVariables

  override val toString = domain.fullName

  def isCompatible(other : DataType) =
    other match{
      case ReferenceDataType() => true
      case _ => false
    }

  override def substitute(s:TypeVariableSubstitution) =  this

  override def equals(other : Any) : Boolean =
  {
    other match{
      case t : ReferenceDataType => true
      case _ => false
    }
  }
  override def hashCode() : Int = domain.fullName.hashCode()
}
