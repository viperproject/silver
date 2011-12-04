package silAST.expressions.terms

import scala.collection.Set
import silAST.source.SourceLocation

import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.programs.symbols.{Field, ProgramVariable,Function}
import silAST.types.{DataTypeFactory, DataType}
import silAST.expressions.util.{PTermSequenceC, PTermSequence, GTermSequence}

protected[silAST] trait PTermFactory extends NodeFactory with GTermFactory with DataTypeFactory
{
  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(sl : SourceLocation, v : ProgramVariable) : ProgramVariableTerm =
  {
    require(programVariables.contains(v))
    addTerm(new ProgramVariableTerm(sl,v))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldProgramVariableTerm(sl : SourceLocation, v : ProgramVariable) : OldProgramVariableTerm =
  {
    //TODO: ensure v has an old version
    require(programVariables.contains(v))
    addTerm(new OldProgramVariableTerm(sl,v))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFunctionApplicationTerm(sl : SourceLocation, r : PTerm,  f : Function,  a : PTermSequence) : PFunctionApplicationTerm =
  {
    require(terms.contains(r))
    require(functions.contains(f))
    require(termSequences.contains(a))
    //TODO: signature check arguments

    addTerm(new PFunctionApplicationTerm(sl,r,f,a))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePCastTerm(sl : SourceLocation, t : PTerm, dt : DataType) : PCastTerm =
  {
    require(terms.contains(t))
    require(dataTypes.contains(dt))
    //TODO: type check arguments

    addTerm(new PCastTerm(sl,t,dt))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFieldReadTerm(sl : SourceLocation, t : PTerm, f : Field) : PFieldReadTerm =
  {
    require(terms.contains(t))
    require(fields.contains(f))
    //TODO: type check arguments

    addTerm(new PFieldReadTerm(sl,t,f))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePOldFieldReadTerm(sl : SourceLocation, t : PTerm, f : Field) : POldFieldReadTerm =
  {
    require(terms.contains(t))
    require(fields.contains(f))
    //TODO: type check

    addTerm(new POldFieldReadTerm(sl,t,f))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePDomainFunctionApplicationTerm(sl : SourceLocation, f : DomainFunction, a : PTermSequence) : PDomainFunctionApplicationTerm =
  {
    require(termSequences.contains(a))
    require(domainFunctions(f.name) == f)

    a match{
      case a : GTermSequence => makeGDomainFunctionApplicationTerm(sl,f,a)
      case _ => addTerm(new PDomainFunctionApplicationTermC(sl,f,a))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////
  def makePTermSequence(sl : SourceLocation, ts : Seq[PTerm]) : PTermSequence = {
    require( ts.toSet subsetOf terms)
    val result = new PTermSequenceC(sl,ts)
    termSequences += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def functions : Set[Function]

  protected[silAST] def programVariables : Set[ProgramVariable]
  protected[silAST] def fields : Set[Field]
  }