package silAST.types
import silAST.domains._
import silAST.expressions.util.TermSequence
import silAST.source.noLocation

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Integer
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
object integerDomain extends Domain(noLocation)
{
  override val name = "Integer"
  override def functions = Set[DomainFunction](integerAddition,integerSubtraction,integerMultiplication,integerDivision,integerNegation)
  override def predicates = Set(integerEQ,integerNE,integerLE,integerLT,integerGE,integerGT)

  override def subNodes = functions ++ predicates
}

object integerType extends NonReferenceDataType(noLocation,integerDomain,DataTypeSequence())


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
}
