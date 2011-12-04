package silAST.domains

import silAST.programs.{NodeFactory, ProgramFactory}
import silAST.expressions.terms.Term
import silAST.source.SourceLocation
import silAST.expressions.{DExpression, Expression, DExpressionFactory}
import collection.mutable.{HashMap, HashSet}
import silAST.types.{DataTypeFactory, DataTypeSequence, DataType}

final class DomainFactory private[silAST](
     val programFactory: ProgramFactory,
     val name: String
     ) extends NodeFactory with DExpressionFactory with DataTypeFactory
{
  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunctionSignature(sl : SourceLocation, p : DataTypeSequence, r : DataType) : DomainFunctionSignature =
  {
    require (dataTypeSequences.contains(p))
    require (dataTypes.contains(r))
    val result = new DomainFunctionSignature(sl,p,r)
    domainFunctionSignatures += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainFunction(sl : SourceLocation, name : String, s : DomainFunctionSignature) =
  {
    require(!domainFunctions.contains(name))
    require(domainFunctionSignatures.contains(s))
    val result = new DomainFunction(sl,name,s)
    domainFunctions += name -> result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicateSignature(sl : SourceLocation, p : DataTypeSequence) : DomainPredicateSignature =
  {
    require (dataTypeSequences.contains(p))
    val result = new DomainPredicateSignature(sl,p)
    domainPredicateSignatures += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def defineDomainPredicate(sl : SourceLocation, name : String, s : DomainPredicateSignature) =
  {
    require(!domainPredicates.contains(name))
    require(domainPredicateSignatures.contains(s))
    val result = new DomainPredicate(sl,name,s)
    domainPredicates += name -> result
    result
  }
  //TODO: add functions/predicates to parent program

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def addDomainAxiom(sl : SourceLocation, name : String, e : DExpression) : DomainAxiom =
  {
    require(!domainAxioms.contains(name))
    val result = new DomainAxiom(sl,name,e)
    domainAxioms += name -> result
    result
  }
  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] override def addTerm[T <: Term](t: T): T = {
    programFactory.addTerm(t)
    super.addTerm(t)
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] override def addExpression[E <: Expression](e: E)  : E = {
    programFactory.addExpression(e)
    super.addExpression(e)
  }

  /////////////////////////////////////////////////////////////////////////
  def domain = if (compiled) pDomain.get else throw new Exception("domain \""+name+"\" not compiled")

  /////////////////////////////////////////////////////////////////////////
  var compiled = false
  var pDomain : Option[Domain] = None

  protected[silAST] val domainFunctionSignatures = new HashSet[DomainFunctionSignature]
  protected[silAST] val domainPredicateSignatures = new HashSet[DomainPredicateSignature]

  protected[silAST] val domainAxioms = new HashMap[String, DomainAxiom]
}
