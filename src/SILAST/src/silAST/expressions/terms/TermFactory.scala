package silAST.expressions.terms

import silAST.source.SourceLocation
import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.expressions.util._
import silAST.programs.symbols.{PredicateFactory, FunctionFactory, Field}
import silAST.types._

protected[silAST] trait TermFactory extends NodeFactory with PTermFactory with DTermFactory {
  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(sourceLocation : SourceLocation, r: Term, ff: FunctionFactory, a: TermSequence): FunctionApplicationTerm = {
    require(terms contains r)
    require(functions contains ff.pFunction)
    require(a.forall(terms contains _))

    (r, a) match {
      case (r: PTerm, a: PTermSequence) => makePFunctionApplicationTerm(sourceLocation, r, ff, a)
      case _ => addTerm(new FunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingTerm(sourceLocation : SourceLocation, r: Term, p: PredicateFactory, t: Term): UnfoldingTerm = {
    require(predicates contains p.pPredicate)
    require(terms contains r)
    require(terms contains t)

    (r, t) match {
      case (r: PTerm, t: PTerm) => makePUnfoldingTerm(sourceLocation, r, p, t)
      case _ => addTerm(new UnfoldingTerm(r, p.pPredicate, t)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(sourceLocation : SourceLocation, t: Term, dt: DataType): CastTerm = {
    require(terms contains t)
    require(dataTypes contains dt)

    t match {
      case t: PTerm => makePCastTerm(sourceLocation, t, dt)
      case _ => addTerm(new CastTerm(t, dt)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(sourceLocation : SourceLocation, t: Term, f: Field): FieldReadTerm = {
    require(terms contains t)
    require(fields contains f)

    t match {
      case t: PTerm => makePFieldReadTerm(sourceLocation, t, f)
      case _ => addTerm(new FieldReadTerm(t, f)(sourceLocation))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldTerm(sourceLocation : SourceLocation, t: Term): OldTerm = {
    require(terms contains t)
    addTerm(new OldTerm(t)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: TermSequence): DomainFunctionApplicationTerm = {
    require(a.forall(terms contains _))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sourceLocation, f, a)
      case a: PTermSequence => makePDomainFunctionApplicationTerm(sourceLocation, f, a)
      case a: DTermSequence => makeDDomainFunctionApplicationTerm(sourceLocation, f, a)
      case _ => addTerm(new DomainFunctionApplicationTerm(f, a)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermTerm(sourceLocation : SourceLocation, location: Term,  field: Field): PermTerm = {
    require (terms contains location)
    require (fields contains field)
    require (location.dataType == referenceType)

    val result = new PermTerm(location,field)(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermission(sourceLocation : SourceLocation, percentage: Term): Term = {
    val result = new DomainFunctionApplicationTerm(percentagePermission, TermSequence(percentage))(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeFullPermission(sourceLocation : SourceLocation): FullPermissionTerm = {
    val result = new FullPermissionTerm()(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeNoPermission(sourceLocation : SourceLocation): NoPermissionTerm = {
    val result = new NoPermissionTerm()(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeEpsilonPermission(sourceLocation : SourceLocation): EpsilonPermissionTerm = {
    val result = new EpsilonPermissionTerm()(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionTerm(sourceLocation : SourceLocation, t1: Term, t2: Term) =
    makeDomainFunctionApplicationTerm(sourceLocation, permissionAddition, TermSequence(t1, t2))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionTerm(sourceLocation : SourceLocation, t1: Term, t2: Term) =
    makeDomainFunctionApplicationTerm(sourceLocation, permissionSubtraction, TermSequence(t1, t2))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationTerm(sourceLocation : SourceLocation, t1: Term, t2: Term) =
    makeDomainFunctionApplicationTerm(sourceLocation, permissionMultiplication, TermSequence(t1, t2))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationTerm(sourceLocation : SourceLocation, t1: Term, i: Term) =
    makeDomainFunctionApplicationTerm(sourceLocation, permissionIntegerMultiplication, TermSequence(t1, i))
}