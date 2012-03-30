package silAST.expressions.terms

import silAST.source.SourceLocation
import silAST.domains.DomainFunction
import silAST.programs.NodeFactory
import silAST.expressions.util._
import silAST.types._
import collection.immutable
import silAST.programs.symbols.{ProgramVariable, PredicateFactory, FunctionFactory, Field}
import silAST.expressions.{ProgramVariableSubstitutionC, ProgramVariableSubstitution}

protected[silAST] trait TermFactory extends NodeFactory with PTermFactory with DTermFactory with GTermFactory{
  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableSubstitution(subs:immutable.Set[(ProgramVariable,Term)]) : ProgramVariableSubstitution =
  {
    subs.foreach(kv => migrate(kv._2))
    new ProgramVariableSubstitutionC(this,subs,immutable.Set())
  }
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateP(t : PTerm)
  {
    super[PTermFactory].migrate(t)
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t : Term)
  {
    if (terms contains t)
      return;
    t match
    {
      case gt : GTerm => super[GTermFactory].migrate(gt)
      case dt : DTerm => super.migrate(dt)
      case pt : PTerm => super.migrate(pt)
      case fa : DomainFunctionApplicationTerm =>
      {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case fa : FunctionApplicationTerm => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case ct : CastTerm => {
        migrate(ct.operand1)
        migrate(ct.newType)
        addTerm(t)
      }
      case fr : FieldReadTerm => {
        require (fields contains fr.field)
        migrate (fr.location)
        addTerm(fr)
      }
      case ut : UnfoldingTerm => {
        require (predicates contains ut.predicate)
        migrate (ut.receiver)
        migrate(ut.term)
        addTerm(ut)
      }
      case ot : OldTerm => {
        migrate (ot.term)
        addTerm(ot)
      }
      case pt  : PermTerm => {
        migrate(pt.location)
        require (fields contains pt.field)
        addTerm(pt)
      }
      case itet : IfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pTerm)
        migrate(itet.nTerm)
      }

    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(r: Term, ff: FunctionFactory, a: TermSequence)(sourceLocation : SourceLocation): FunctionApplicationTerm = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate (_))

    (r, a) match {
      case (r: PTerm, a: PTermSequence) => makePFunctionApplicationTerm(r, ff, a)(sourceLocation)
      case _ => addTerm(new FunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingTerm(r: Term, p: PredicateFactory, t: Term)(sourceLocation : SourceLocation): UnfoldingTerm = {
    require(predicates contains p.pPredicate)
    migrate(r)
    migrate(t)

    (r, t) match {
      case (r: PTerm, t: PTerm) => makePUnfoldingTerm(r, p, t)(sourceLocation)
      case _ => addTerm(new UnfoldingTerm(r, p.pPredicate, t)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(t: Term, dt: DataType)(sourceLocation : SourceLocation): CastTerm = {
    migrate(dt)
    migrate(t)

    t match {
      case t: PTerm => makePCastTerm(t, dt)(sourceLocation)
      case _ => addTerm(new CastTerm(t, dt)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(t: Term, f: Field)(sourceLocation : SourceLocation): FieldReadTerm = {
    require(fields contains f)
    migrate(t)

    t match {
      case t: PTerm => makePFieldReadTerm(t, f)(sourceLocation)
      case _ => addTerm(new FieldReadTerm(t, f)(sourceLocation))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldTerm(t: Term)(sourceLocation : SourceLocation): OldTerm = {
    migrate(t)
    require(t.programVariables intersect outputProgramVariables isEmpty)
    addTerm(new OldTerm(t)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(f: DomainFunction, a: TermSequence)(sourceLocation : SourceLocation): DomainFunctionApplicationTerm = {
    require(domainFunctions contains f)
    a.foreach(migrate (_))

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(f, a)(sourceLocation)
      case a: PTermSequence => makePDomainFunctionApplicationTerm(f, a)(sourceLocation)
      case a: DTermSequence => makeDDomainFunctionApplicationTerm(f, a)(sourceLocation)
      case _ => addTerm(new DomainFunctionApplicationTerm(f, a)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermTerm(location: Term,  field: Field)(sourceLocation : SourceLocation): PermTerm = {
    migrate(location)
    require (fields contains field)
    require (location.dataType == referenceType)

    val result = new PermTerm(location,field)(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermission(percentage: Term)(sourceLocation : SourceLocation): Term = {
    val result = new DomainFunctionApplicationTerm(percentagePermission, TermSequence(percentage))(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeFullPermission()(sourceLocation : SourceLocation): FullPermissionTerm = {
    val result = new FullPermissionTerm()(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeNoPermission()(sourceLocation : SourceLocation): NoPermissionTerm = {
    val result = new NoPermissionTerm()(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeEpsilonPermission()(sourceLocation : SourceLocation): EpsilonPermissionTerm = {
    val result = new EpsilonPermissionTerm()(sourceLocation)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionTerm(t1: Term, t2: Term)(sourceLocation : SourceLocation) =
    makeDomainFunctionApplicationTerm(permissionAddition, TermSequence(t1, t2))(sourceLocation)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionTerm(t1: Term, t2: Term)(sourceLocation : SourceLocation) =
    makeDomainFunctionApplicationTerm(permissionSubtraction, TermSequence(t1, t2))(sourceLocation)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationTerm(t1: Term, t2: Term)(sourceLocation : SourceLocation) =
    makeDomainFunctionApplicationTerm(permissionMultiplication, TermSequence(t1, t2))(sourceLocation)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationTerm(t1: Term, i: Term)(sourceLocation : SourceLocation) =
    makeDomainFunctionApplicationTerm(permissionIntegerMultiplication, TermSequence(t1, i))(sourceLocation)

  /////////////////////////////////////////////////////////////////////////
  def makeIfThenElseTerm(c : Term,  p:Term,  n : Term)(sourceLocation : SourceLocation): IfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc:GTerm, gp:GTerm,gn:GTerm) => makeGIfThenElseTerm(gc,gp,gn)(sourceLocation)
      case (dc:DTerm, dp:DTerm,dn:DTerm) => makeDIfThenElseTerm(dc,dp,dn)(sourceLocation)
      case (pc:PTerm, pp:PTerm,pn:PTerm) => makePIfThenElseTerm(pc,pp,pn)(sourceLocation)
      case _ => addTerm(new IfThenElseTerm(c,p,n)(sourceLocation))
    }
  }
}