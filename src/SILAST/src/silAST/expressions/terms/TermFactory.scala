package silAST.expressions.terms

import silAST.source.SourceLocation
import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.expressions.util._
import silAST.programs.symbols.{PredicateFactory, FunctionFactory, Field}
import silAST.types._

protected[silAST] trait TermFactory extends NodeFactory with PTermFactory with DTermFactory
{
  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(sl: SourceLocation, r: Term, ff: FunctionFactory, a: TermSequence): FunctionApplicationTerm = {
    require(terms contains r)
    require(functions contains ff.pFunction)
    require(a.forall(terms contains _))
    //TODO: signature check parameters

    (r, a) match {
      case (r: PTerm, a: PTermSequence) => makePFunctionApplicationTerm(sl, r, ff, a)
      case _ => addTerm(new FunctionApplicationTerm(sl, r, ff.pFunction, a))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingTerm(sl: SourceLocation, r: Term, p : PredicateFactory, t: Term): UnfoldingTerm = {
    require(predicates contains p.pPredicate)
    require(terms contains r)
    require(terms contains t)

    (r, t) match {
      case (r: PTerm,  t: PTerm ) => makePUnfoldingTerm(sl,r,p,t)
      case _ => addTerm(new UnfoldingTerm(sl, r,p.pPredicate, t))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(sl: SourceLocation, t: Term, dt: DataType): CastTerm = {
    require(terms contains t)
    require(dataTypes contains dt)
    //TODO: type check parameters

    t match {
      case t: PTerm => makePCastTerm(sl, t, dt)
      case _ => addTerm(new CastTerm(sl, t, dt))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(sl: SourceLocation, t: Term, f: Field): FieldReadTerm = {
    require(terms contains t)
    require(fields contains f)
    //TODO: type check parameters

    t match {
      case t: PTerm => makePFieldReadTerm(sl, t, f)
      case _ => addTerm(new FieldReadTerm(sl, t, f))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldTerm(sl: SourceLocation, t: Term): OldTerm = {
    require(terms contains t)
    addTerm(new OldTerm(sl,t))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(sl: SourceLocation, f: DomainFunction, a: TermSequence): DomainFunctionApplicationTerm = {
    require(a.forall(terms contains _))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sl, f, a)
      case a: PTermSequence => makePDomainFunctionApplicationTerm(sl, f, a)
      case a: DTermSequence => makeDDomainFunctionApplicationTerm(sl, f, a)
      case _ => addTerm(new DomainFunctionApplicationTerm(sl, f, a))
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermission(sl: SourceLocation, percentage: Term): Term = {
    val result = new DomainFunctionApplicationTerm(sl,percentagePermission,TermSequence(percentage))
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionTerm(sl: SourceLocation, t1: Term, t2: Term)=
    makeDomainFunctionApplicationTerm(sl,permissionAddition,TermSequence(t1,t2))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionTerm(sl: SourceLocation, t1: Term, t2: Term) =
    makeDomainFunctionApplicationTerm(sl,permissionSubtraction,TermSequence(t1,t2))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationTerm(sl: SourceLocation, t1: Term, t2: Term) =
    makeDomainFunctionApplicationTerm(sl,permissionMultiplication,TermSequence(t1,t2))

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationTerm(sl: SourceLocation,t1: Term, i: Term) =
    makeDomainFunctionApplicationTerm(sl,permissionIntegerMultiplication,TermSequence(t1,i))

}