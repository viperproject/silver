package silAST.expressions.terms

import scala.collection.Set
import silAST.source.SourceLocation

import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.types.{DataTypeFactory, DataType}
import silAST.expressions.util.{PTermSequenceC, PTermSequence, GTermSequence}
import silAST.expressions.{UnfoldingExpression, Expression}
import silAST.programs.symbols._

protected[silAST] trait PTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {
  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(sl: SourceLocation, v: ProgramVariable): ProgramVariableTerm = {
    require(programVariables.contains(v))
    addTerm(new ProgramVariableTerm(sl, v))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldProgramVariableTerm(sl: SourceLocation, v: ProgramVariable): OldProgramVariableTerm = {
    //TODO: ensure v has an old version
    require(programVariables.contains(v))
    addTerm(new OldProgramVariableTerm(sl, v))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFunctionApplicationTerm(sl: SourceLocation, r: PTerm, ff: FunctionFactory, a: PTermSequence): PFunctionApplicationTerm = {
    require(terms contains r)
    require(functions contains ff.pFunction)
    require(a.forall(terms contains _))
    //TODO: signature check arguments

    addTerm(new PFunctionApplicationTerm(sl, r, ff.pFunction, a))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePCastTerm(sl: SourceLocation, t: PTerm, dt: DataType): PCastTerm = {
    require(terms contains t)
    require(dataTypes contains dt)
    //TODO: type check arguments

    addTerm(new PCastTerm(sl, t, dt))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFieldReadTerm(sl: SourceLocation, t: PTerm, f: Field): PFieldReadTerm = {
    require(terms.contains(t))
    require(fields.contains(f))
    //TODO: type check arguments

    addTerm(new PFieldReadTerm(sl, t, f))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePOldFieldReadTerm(sl: SourceLocation, t: PTerm, f: Field): POldFieldReadTerm = {
    require(terms.contains(t))
    require(fields.contains(f))
    //TODO: type check

    addTerm(new POldFieldReadTerm(sl, t, f))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePDomainFunctionApplicationTerm(sl: SourceLocation, f: DomainFunction, a: PTermSequence): PDomainFunctionApplicationTerm = {
    require(a.forall(terms contains _))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sl, f, a)
      case _ => addTerm(new PDomainFunctionApplicationTermC(sl, f, a))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingTerm(sl: SourceLocation, r: PTerm, p : PredicateFactory, t: PTerm): PUnfoldingTerm = {
    require(predicates contains p.pPredicate)
    require(terms contains r)
    require(terms contains t)

    addTerm(new PUnfoldingTerm(sl, r,p.pPredicate, t))
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def functions: Set[Function]

  def nullFunction: DomainFunction

  protected[silAST] def programVariables: Set[ProgramVariable]

  protected[silAST] def fields: Set[Field]
  protected[silAST] def predicates: Set[Predicate]
}