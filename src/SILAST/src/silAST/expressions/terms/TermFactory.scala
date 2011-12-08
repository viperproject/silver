package silAST.expressions.terms

import silAST.source.SourceLocation
import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.types.DataType
import silAST.expressions.util._
import silAST.programs.symbols.{PredicateFactory, Predicate, FunctionFactory, Field}

protected[silAST] trait TermFactory extends NodeFactory with PTermFactory with DTermFactory {
  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(sl: SourceLocation, r: Term, ff: FunctionFactory, a: TermSequence): FunctionApplicationTerm = {
    require(terms.contains(r))
    require(functions.contains(ff.pFunction))
    require(a.forall(terms contains _))
    //TODO: signature check arguments

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
    require(terms.contains(t))
    require(dataTypes.contains(dt))
    //TODO: type check arguments

    t match {
      case t: PTerm => makePCastTerm(sl, t, dt)
      case _ => addTerm(new CastTerm(sl, t, dt))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(sl: SourceLocation, t: Term, f: Field): FieldReadTerm = {
    require(terms.contains(t))
    require(fields.contains(f))
    //TODO: type check arguments

    t match {
      case t: PTerm => makePFieldReadTerm(sl, t, f)
      case _ => addTerm(new FieldReadTerm(sl, t, f))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldFieldReadTerm(sl: SourceLocation, t: Term, f: Field): OldFieldReadTerm = {
    require(terms contains t)
    require(fields contains f)
    //TODO: type check

    t match {
      case t: PTerm => makePOldFieldReadTerm(sl, t, f)
      case _ => addTerm(new OldFieldReadTerm(sl, t, f))
    }
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

}