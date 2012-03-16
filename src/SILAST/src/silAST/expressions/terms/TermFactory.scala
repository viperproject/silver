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
  def makeFunctionApplicationTerm(sourceLocation : SourceLocation, r: Term, ff: FunctionFactory, a: TermSequence): FunctionApplicationTerm = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate (_))

    (r, a) match {
      case (r: PTerm, a: PTermSequence) => makePFunctionApplicationTerm(sourceLocation, r, ff, a)
      case _ => addTerm(new FunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingTerm(sourceLocation : SourceLocation, r: Term, p: PredicateFactory, t: Term): UnfoldingTerm = {
    require(predicates contains p.pPredicate)
    migrate(r)
    migrate(t)

    (r, t) match {
      case (r: PTerm, t: PTerm) => makePUnfoldingTerm(sourceLocation, r, p, t)
      case _ => addTerm(new UnfoldingTerm(r, p.pPredicate, t)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(sourceLocation : SourceLocation, t: Term, dt: DataType): CastTerm = {
    migrate(dt)
    migrate(t)

    t match {
      case t: PTerm => makePCastTerm(sourceLocation, t, dt)
      case _ => addTerm(new CastTerm(t, dt)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(sourceLocation : SourceLocation, t: Term, f: Field): FieldReadTerm = {
    require(fields contains f)
    migrate(t)

    t match {
      case t: PTerm => makePFieldReadTerm(sourceLocation, t, f)
      case _ => addTerm(new FieldReadTerm(t, f)(sourceLocation))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldTerm(sourceLocation : SourceLocation, t: Term): OldTerm = {
    migrate(t)
    addTerm(new OldTerm(t)(sourceLocation))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(sourceLocation : SourceLocation, f: DomainFunction, a: TermSequence): DomainFunctionApplicationTerm = {
    require(domainFunctions contains f)
    a.foreach(migrate (_))

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(sourceLocation, f, a)
      case a: PTermSequence => makePDomainFunctionApplicationTerm(sourceLocation, f, a)
      case a: DTermSequence => makeDDomainFunctionApplicationTerm(sourceLocation, f, a)
      case _ => addTerm(new DomainFunctionApplicationTerm(f, a)(sourceLocation))
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermTerm(sourceLocation : SourceLocation, location: Term,  field: Field): PermTerm = {
    migrate(location)
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

  /////////////////////////////////////////////////////////////////////////
  def makeIfThenElseTerm(sourceLocation : SourceLocation, c : Term,  p:Term,  n : Term): IfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc:GTerm, gp:GTerm,gn:GTerm) => makeGIfThenElseTerm(sourceLocation,gc,gp,gn)
      case (dc:DTerm, dp:DTerm,dn:DTerm) => makeDIfThenElseTerm(sourceLocation,dc,dp,dn)
      case (pc:PTerm, pp:PTerm,pn:PTerm) => makePIfThenElseTerm(sourceLocation,pc,pp,pn)
      case _ => addTerm(new IfThenElseTerm(c,p,n)(sourceLocation))
    }
  }
}