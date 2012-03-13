package silAST.expressions.terms

import silAST.source.SourceLocation

import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.expressions.util.{PTermSequence, GTermSequence}
import silAST.programs.symbols._
import silAST.types.{booleanType, DataTypeFactory, DataType}
import collection.{immutable, Set}
import silAST.expressions.{PProgramVariableSubstitutionC, PProgramVariableSubstitution}

protected[silAST] trait PTermFactory extends NodeFactory with GTermFactory with DataTypeFactory {
  def makePProgramVariableSubstitution(subs:immutable.Set[(ProgramVariable,PTerm)]) : PProgramVariableSubstitution =
  {
    subs.foreach(kv => migrateP(kv._2))
    new PProgramVariableSubstitutionC(this,subs,immutable.Set())
  }


  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateP(t : PTerm)
  {
    if (terms contains t)
      return;
    t match
    {
      case gt : GTerm => migrateG(gt)
      case pv : ProgramVariableTerm => {
        require (programVariables contains pv.variable)
        addTerm(pv)
      }
      case fa : PFunctionApplicationTerm => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrateP(_))
        addTerm(fa)
      }
      case dfa : PDomainFunctionApplicationTerm => {
        dfa.arguments.foreach(migrateP(_))
        require(domainFunctions contains dfa.function)
        addTerm(dfa)
      }
      case ct : PCastTerm => {
        migrateP(ct.operand1)
        migrate(ct.newType)
        addTerm(t)
      }
      case fr : PFieldReadTerm => {
        require (fields contains fr.field)
        migrateP (fr.location)
        addTerm(fr)
      }
      case ut : PUnfoldingTerm => {
        require (predicates contains ut.predicate)
        migrateP (ut.receiver)
        migrateP(ut.term)
        addTerm(ut)
      }
      case itet : PIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrateP(itet.condition)
        migrateP(itet.pTerm)
        migrateP(itet.nTerm)
      }
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(sourceLocation : SourceLocation, v: ProgramVariable): ProgramVariableTerm = {
    require(programVariables contains v)
    addTerm(new ProgramVariableTerm(v)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFunctionApplicationTerm(sourceLocation : SourceLocation, r: PTerm, ff: FunctionFactory, a: PTermSequence): PFunctionApplicationTerm = {
    migrateP(r)
    require(functions contains ff.pFunction)
    a.foreach(migrateP(_))

    addTerm(new PFunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePCastTerm(sourceLocation : SourceLocation, t: PTerm, dt: DataType): PCastTerm = {
    migrateP(t)
    migrate(dt)

    addTerm(new PCastTerm(t, dt)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFieldReadTerm(sourceLocation : SourceLocation, t: PTerm, f: Field): PFieldReadTerm = {
    migrateP(t)
    require(fields contains f)

    addTerm(new PFieldReadTerm(t, f)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: PTermSequence): PDomainFunctionApplicationTerm = {
    a.foreach(migrateP (_))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sourceLocation, f, a)
      case _ => addTerm(new PDomainFunctionApplicationTermC(f, a)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingTerm(sourceLocation : SourceLocation, r: PTerm, p: PredicateFactory, t: PTerm): PUnfoldingTerm = {
    require(predicates contains p.pPredicate)
    migrateP(r)
    migrateP(t)

    addTerm(new PUnfoldingTerm(r, p.pPredicate, t)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePIfThenElseTerm(sourceLocation : SourceLocation, c : PTerm,  p:PTerm,  n : PTerm): PIfThenElseTerm = {
    migrateP(c)
    migrateP(p)
    migrateP(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc:GTerm, gp:GTerm,gn:GTerm) => makeGIfThenElseTerm(sourceLocation,gc,gp,gn)
      case _ => addTerm(new PIfThenElseTermC(c,p,n)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def functions: Set[Function]

  protected[silAST] def programVariables: Set[ProgramVariable]

  protected[silAST] def fields: Set[Field]

  protected[silAST] def predicates: Set[Predicate]
}