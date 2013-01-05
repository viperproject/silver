package semper.sil.ast.types

import semper.sil.ast.ASTNode
import semper.sil.ast.source.{noLocation, SourceLocation}
import semper.sil.ast.domains.{DomainTemplate, TypeVariableSubstitution, Domain}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
sealed abstract class DataType extends ASTNode {
  def isCompatible(other: DataType): Boolean

  def substitute(s: TypeVariableSubstitution): DataType = this

  def freeTypeVariables: collection.immutable.Set[TypeVariable] = Set()

  def domain: Domain

  override def equals(other: Any): Boolean

  override def hashCode(): Int
}


/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
final class TypeVariable private[sil](val name: String, val domainTemplate: DomainTemplate)(val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode {
  override val toString = name

  override def equals(other: Any): Boolean = {
    other match {
      case v: TypeVariable => this eq v
      case _ => false
    }
  }

  override def hashCode(): Int = name.hashCode()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
final case class VariableType(
                               variable: TypeVariable
                               )(override val sourceLocation: SourceLocation, override val comment: List[String]) extends DataType {
  override val toString = variable.name

  override def isCompatible(other: DataType) =
    other match {
      case VariableType(v) => v == variable
      case _ => false
    }

  override def substitute(s: TypeVariableSubstitution) = {
    var result = s.mapType(variable, this)
    result
  }

  override def freeTypeVariables = Set(variable)

  override lazy val domain = variable.domainTemplate.domain

  override def equals(other: Any): Boolean = {
    other match {
      case v: VariableType => variable == v.variable
      case _ => false
    }
  }

  override def hashCode(): Int = variable.hashCode()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
case class NonReferenceDataType private[sil](
                                              domain: Domain
                                              )(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends DataType {
  require(domain ne referenceDomain)

  override def freeTypeVariables = domain.freeTypeVariables

  override val toString = domain.fullName

  def isCompatible(other: DataType) =
    other match {
      case NonReferenceDataType(d) => domain.isCompatible(d)
      case _ => false
    }

  override def substitute(s: TypeVariableSubstitution) = {

    val result = if (s.typeVariables.intersect(freeTypeVariables).isEmpty)
      this
    else
      new NonReferenceDataType(domain.substitute(s))(s.sourceLocation(sourceLocation), Nil)

    result
  }

  override def equals(other: Any): Boolean = {
    other match {
      case t: NonReferenceDataType => domain == t.domain
      case _ => false
    }
  }

  override def hashCode(): Int = domain.fullName.hashCode()
}

/////////////////////////////////////////////////////////////////////
/////////////////////////////////////////////////////////////////////
case class ReferenceDataType private[sil]() extends DataType {
  override val sourceLocation = noLocation
  override val comment = Nil
  val domain: Domain = referenceDomain

  override def freeTypeVariables = domain.freeTypeVariables

  override val toString = domain.fullName

  def isCompatible(other: DataType) =
    other match {
      case ReferenceDataType() => true
      case _ => false
    }

  override def substitute(s: TypeVariableSubstitution) = this

  override def equals(other: Any): Boolean = {
    other match {
      case t: ReferenceDataType => true
      case _ => false
    }
  }

  override def hashCode(): Int = domain.fullName.hashCode()
}
