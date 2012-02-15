package silAST.expressions.terms

import scala.collection.Set
import silAST.source.SourceLocation

import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.types.{DataTypeFactory, DataType}
import silAST.expressions.util.{PTermSequence, GTermSequence}
import silAST.programs.symbols._

protected[silAST] trait PTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {
  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(sourceLocation : SourceLocation, v: ProgramVariable): ProgramVariableTerm = {
    require(programVariables contains v)
    addTerm(new ProgramVariableTerm(v)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFunctionApplicationTerm(sourceLocation : SourceLocation, r: PTerm, ff: FunctionFactory, a: PTermSequence): PFunctionApplicationTerm = {
    require(terms contains r)
    require(functions contains ff.pFunction)
    require(a.forall(terms contains _))

    addTerm(new PFunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePCastTerm(sourceLocation : SourceLocation, t: PTerm, dt: DataType): PCastTerm = {
    require(terms contains t)
    require(dataTypes contains dt)

    addTerm(new PCastTerm(t, dt)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFieldReadTerm(sourceLocation : SourceLocation, t: PTerm, f: Field): PFieldReadTerm = {
    require(terms contains t)
    require(fields contains f)

    addTerm(new PFieldReadTerm(t, f)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: PTermSequence): PDomainFunctionApplicationTerm = {
    require(a.forall(terms contains _))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sourceLocation, f, a)
      case _ => addTerm(new PDomainFunctionApplicationTermC(f, a)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingTerm(sourceLocation : SourceLocation, r: PTerm, p: PredicateFactory, t: PTerm): PUnfoldingTerm = {
    require(predicates contains p.pPredicate)
    require(terms contains r)
    require(terms contains t)

    addTerm(new PUnfoldingTerm(r, p.pPredicate, t)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def functions: Set[Function]

  protected[silAST] def programVariables: Set[ProgramVariable]

  protected[silAST] def fields: Set[Field]

  protected[silAST] def predicates: Set[Predicate]
}