package silAST.expressions.terms

import silAST.source.SourceLocation
import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.types.DataType
import silAST.programs.symbols.{Field,Function}
import silAST.expressions.util.{DTermSequence, TermSequence, PTermSequence, GTermSequence}

protected[silAST] trait TermFactory extends NodeFactory with PTermFactory with DTermFactory
{
  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(sl : SourceLocation, r : Term,  f : Function,  a : TermSequence) : FunctionApplicationTerm =
  {
    require(terms.contains(r))
    require(functions.contains(f))
    require(termSequences.contains(a))
    //TODO: signature check arguments

    (r,a) match {
      case (r:PTerm,  a : PTermSequence ) => makePFunctionApplicationTerm (sl,r,f,a)
      case _ => addTerm(new FunctionApplicationTerm(sl,r,f,a))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(sl : SourceLocation, t : Term, dt : DataType) : CastTerm =
  {
    require(terms.contains(t))
    require(dataTypes.contains(dt))
    //TODO: type check arguments

    t match{
      case t : PTerm => makePCastTerm(sl,t,dt)
      case _ => addTerm(new CastTerm(sl,t,dt))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(sl : SourceLocation, t : Term, f : Field) : FieldReadTerm =
  {
    require(terms.contains(t))
    require(fields(f.name) == f)
    //TODO: type check arguments

    t match {
      case t : PTerm => makePFieldReadTerm(sl,t,f)
      case _ => addTerm(new FieldReadTerm(sl,t,f))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldFieldReadTerm(sl : SourceLocation, t : Term, f : Field) : OldFieldReadTerm =
  {
    require(terms.contains(t))
    require(fields(f.name) == f)
    //TODO: type check

    t match {
      case t : PTerm => makePOldFieldReadTerm(sl,t,f)
      case _ => addTerm(new OldFieldReadTerm(sl,t,f))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(sl : SourceLocation, f : DomainFunction, a : TermSequence) : DomainFunctionApplicationTerm =
  {
    require(termSequences.contains(a))
    require(domainFunctions(f.name) == f)

    a match{
      case a : GTermSequence => makeGDomainFunctionApplicationTerm(sl,f,a)
      case a : PTermSequence => makePDomainFunctionApplicationTerm(sl,f,a)
      case a : DTermSequence => makeDDomainFunctionApplicationTerm(sl,f,a)
      case _ => addTerm(new DomainFunctionApplicationTerm(sl,f,a))
    }
  }

}