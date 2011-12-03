package silAST.expressions.terms

import silAST.source.SourceLocation
import collection.mutable.{HashMap, HashSet}
import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.types.DataType
import silAST.expressions.util.{PTermSequence, GTermSequence}
import silAST.programs.symbols.{Field, ProgramVariable,Function}
import silAST.symbols.DataTypeSequence

protected[silAST] trait PTermFactory extends NodeFactory with GTermFactory
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
    require(fields(f.name) == f)
    //TODO: type check arguments

    addTerm(new PFieldReadTerm(sl,t,f))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePOldFieldReadTerm(sl : SourceLocation, t : PTerm, f : Field) : POldFieldReadTerm =
  {
    require(terms.contains(t))
    require(fields(f.name) == f)
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
  protected[silAST] val programVariables = new HashSet[ProgramVariable]
  protected[silAST] val functions = new HashSet[Function]

  protected[silAST] val fields = new HashMap[String, Field]

  protected[silAST] val dataTypes = new HashSet[DataType]
  protected[silAST] val dataTypeSequences = new HashMap[List[DataType], DataTypeSequence]
}