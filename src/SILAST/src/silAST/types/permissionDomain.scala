package silAST.types

import silAST.expressions.util.TermSequence
import silAST.source.noLocation
import silAST.domains._

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Permissions
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

object permissionDomain extends Domain
{
  override val name = "Permission"
  override val sourceLocation = noLocation
  override def fullName : String = name
  override def functions = Set(permissionAddition,permissionSubtraction,permissionMultiplication,permissionIntegerMultiplication)
  override def predicates = Set(permissionEQ,permissionNE,permissionLT,permissionLE, permissionGT,permissionGE)
  override val freeTypeVariables = Set[TypeVariable]()
  override def getType = permissionType
  override val axioms = Set[DomainAxiom]()

  override def isCompatible(other : Domain) = other == permissionDomain
  override def substitute(s:TypeVariableSubstitution) = this
}

object permissionType extends NonReferenceDataType(noLocation,permissionDomain)




///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
object permissionAddition extends DomainFunction
{
  override val sourceLocation = noLocation
  override val name = "+"
  override val signature = new DomainFunctionSignature(noLocation,DataTypeSequence(permissionType,permissionType),permissionType)
  override val domain = permissionDomain
  override def substitute(ts:TypeVariableSubstitution) = this

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "+" + ts(1).toString
  }

}

object percentagePermission extends DomainFunction
{
  override val sourceLocation = noLocation
  override val name = "%"
  override val signature = new DomainFunctionSignature(noLocation,DataTypeSequence(integerType),permissionType)
  override val domain = permissionDomain
  override def substitute(ts:TypeVariableSubstitution) = this

  override def toString(ts : TermSequence) =
  {
    require(ts.length==1)
    ts.head.toString + "%"
  }
}

object permissionSubtraction extends DomainFunction
{
  override val sourceLocation = noLocation
  override val name = "-"
  override val signature = new DomainFunctionSignature(noLocation,DataTypeSequence(permissionType,permissionType),permissionType)
  override val domain = permissionDomain
  override def substitute(ts:TypeVariableSubstitution) = this

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "-" + ts(1).toString
  }
}

object permissionMultiplication extends DomainFunction
{
  override val sourceLocation = noLocation
  override val name = "*"
  override val signature = new DomainFunctionSignature(noLocation,DataTypeSequence(permissionType,permissionType),permissionType)
  override val domain = permissionDomain
  override def substitute(ts:TypeVariableSubstitution) = this

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "*" + ts(1).toString
  }
}

object permissionIntegerMultiplication extends DomainFunction
{
  override val sourceLocation = noLocation
  override val name = "*"
  override val signature = new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,permissionType),permissionType)
  override val domain = permissionDomain
  override def substitute(ts:TypeVariableSubstitution) = this

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "*" + ts(1).toString
  }
}

///////////////////////////////////////////////////////////////////////////
object permissionLE extends DomainPredicate
{
  override val sourceLocation = noLocation
  override val name = "<="
  override val signature = new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
  override lazy val domain = permissionDomain

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "<=" + ts(1).toString
  }
  override def substitute(ts:TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionLT extends DomainPredicate
{
  override val sourceLocation = noLocation
  override val name = "<"
  override val signature = new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
  override lazy val domain = permissionDomain

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "<" + ts(1).toString
  }
  override def substitute(ts:TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionGE extends DomainPredicate
{
  override val sourceLocation = noLocation
  override val name = ">="
  override val signature = new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
  override lazy val domain = permissionDomain

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + ">=" + ts(1).toString
  }
  override def substitute(ts:TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionGT extends DomainPredicate
{
  override val sourceLocation = noLocation
  override val name = ">"
  override val signature = new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
  override lazy val domain = permissionDomain

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + ">" + ts(1).toString
  }
  override def substitute(ts:TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionEQ extends DomainPredicate
{
  override val sourceLocation = noLocation
  override val name = "=="
  override val signature = new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
  override lazy val domain = permissionDomain

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "==" + ts(1).toString
  }
  override def substitute(ts:TypeVariableSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionNE extends DomainPredicate
{
  override val sourceLocation = noLocation
  override val name = "!="
  override val signature = new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
  override lazy val domain = permissionDomain

  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "!=" + ts(1).toString
  }
  override def substitute(ts:TypeVariableSubstitution) = this

}
