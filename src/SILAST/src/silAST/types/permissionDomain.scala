package silAST.types

import silAST.expressions.util.TermSequence
import silAST.source.noLocation
import silAST.domains._

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Permissions
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

object permissionDomain extends Domain(noLocation)
{
  override val name = "Permission"
  override def fullName : String = name
  override def functions = Set(permissionAddition,permissionSubtraction,permissionMultiplication,permissionIntegerMultiplication)
  override def predicates = Set(permissionEQ,permissionNE,permissionLT,permissionLE, permissionGT,permissionGE)
  override val freeTypeVariables = Set[TypeVariable]()
  override def getType = permissionType
  override val axioms = Set[DomainAxiom]()

  override def isCompatible(other : Domain) = other == permissionDomain
  override def substitute(s:TypeSubstitution) = this
}

object permissionType extends NonReferenceDataType(noLocation,permissionDomain)




///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
object permissionAddition extends DomainFunction(
  noLocation,
  "+",
  new DomainFunctionSignature(noLocation,DataTypeSequence(permissionType,permissionType),permissionType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "+" + ts(1).toString
  }
}

object percentagePermission extends DomainFunction(
  noLocation,
  "%",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType),permissionType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==1)
    ts.head.toString + "%"
  }
}

object permissionSubtraction extends DomainFunction(
  noLocation,
  "-",
  new DomainFunctionSignature(noLocation,DataTypeSequence(permissionType,permissionType),permissionType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "-" + ts(1).toString
  }
}

object permissionMultiplication extends DomainFunction(
  noLocation,
  "*",
  new DomainFunctionSignature(noLocation,DataTypeSequence(permissionType,permissionType),permissionType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "*" + ts(1).toString
  }
}

object permissionIntegerMultiplication extends DomainFunction(
  noLocation,
  "*",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,permissionType),permissionType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "*" + ts(1).toString
  }
}

///////////////////////////////////////////////////////////////////////////
object permissionLE extends DomainPredicate(
  noLocation,
  "<=",
  new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "<=" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionLT extends DomainPredicate(
  noLocation,
  "<",
  new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "<" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionGE extends DomainPredicate(
  noLocation,
  ">=",
  new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + ">=" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionGT extends DomainPredicate(
  noLocation,
  ">",
  new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + ">" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionEQ extends DomainPredicate(
  noLocation,
  "==",
  new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "==" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object permissionNE extends DomainPredicate(
  noLocation,
  "!=",
  new DomainPredicateSignature(noLocation,DataTypeSequence(permissionType,permissionType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "!=" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}
