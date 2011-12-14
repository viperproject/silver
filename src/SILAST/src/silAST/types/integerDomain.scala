package silAST.types
import silAST.domains._
import silAST.expressions.util.TermSequence
import silAST.source.noLocation
import silAST.expressions.terms.Term

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Integer
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
object integerDomain extends Domain(noLocation)
{
  override def toString = name
  override val name = "Integer"
  override def functions = Set[DomainFunction](integerAddition,integerSubtraction,integerMultiplication,integerDivision,integerModulo,integerNegation)
  override def predicates = Set(integerEQ,integerNE,integerLE,integerLT,integerGE,integerGT)
  override val axioms = Set.empty[DomainAxiom]
  override def substitute(ts:TypeSubstitution) = this
  override def getType = integerType
  override def freeTypeVariables = Set()
  override def isCompatible(other : Domain) = other == this
}

object integerType extends NonReferenceDataType(noLocation,integerDomain)


///////////////////////////////////////////////////////////////////////////
object integerAddition extends DomainFunction(
  noLocation,
  "+",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,integerType),integerType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "+" + ts(1).toString
  }

  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerSubtraction extends DomainFunction(
  noLocation,
  "-",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,integerType),integerType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "-" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerMultiplication extends DomainFunction(
  noLocation,
  "*",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,integerType),integerType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "*" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerDivision extends DomainFunction(
  noLocation,
  "/",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,integerType),integerType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "/" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerModulo extends DomainFunction(
  noLocation,
  "%",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType,integerType),integerType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "%" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerNegation extends DomainFunction(
  noLocation,
  "-",
  new DomainFunctionSignature(noLocation,DataTypeSequence(integerType),integerType)
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==1)
    "-" + ts(0).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}

///////////////////////////////////////////////////////////////////////////
object integerLE extends DomainPredicate(
  noLocation,
  "<=",
  new DomainPredicateSignature(noLocation,DataTypeSequence(integerType,integerType))
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
object integerLT extends DomainPredicate(
  noLocation,
  "<",
  new DomainPredicateSignature(noLocation,DataTypeSequence(integerType,integerType))
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
object integerGE extends DomainPredicate(
  noLocation,
  ">=",
  new DomainPredicateSignature(noLocation,DataTypeSequence(integerType,integerType))
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
object integerGT extends DomainPredicate(
  noLocation,
  ">",
  new DomainPredicateSignature(noLocation,DataTypeSequence(integerType,integerType))
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
object integerEQ extends DomainPredicate(
  noLocation,
  "==",
  new DomainPredicateSignature(noLocation,DataTypeSequence(integerType,integerType))
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
object integerNE extends DomainPredicate(
  noLocation,
  "!=",
  new DomainPredicateSignature(noLocation,DataTypeSequence(integerType,integerType))
)
{
  override def toString(ts : TermSequence) =
  {
    require(ts.length==2)
    ts(0).toString + "!=" + ts(1).toString
  }
  override def substitute(ts:TypeSubstitution) = this
}
