package silAST.expressions.terms

import silAST.source.SourceLocation
import silAST.programs.NodeFactory
import silAST.expressions.util._
import silAST.types._
import collection.immutable
import silAST.programs.symbols.{ProgramVariable, PredicateFactory, FunctionFactory, Field}
import silAST.symbols.logical.quantification.LogicalVariable
import silAST.domains.{LogicalVariableSubstitutionC, LogicalVariableSubstitution, DomainFunction}
import silAST.expressions.{PredicatePermissionExpression,PPredicatePermissionExpression, ProgramVariableSubstitutionC, ProgramVariableSubstitution}

protected[silAST] trait TermFactory
  extends NodeFactory
  with PTermFactory
  with DTermFactory
  with GTermFactory
{
  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableSubstitution(subs: immutable.Set[(ProgramVariable, Term)]): ProgramVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new ProgramVariableSubstitutionC(subs, Set())
  }

  /////////////////////////////////////////////////////////////////////////
  def makeLogicalVariableSubstitution(subs: immutable.Set[(LogicalVariable, Term)]): LogicalVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new LogicalVariableSubstitutionC(Set(), subs)
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateP(t: PTerm) {
    super[PTermFactory].migrate(t)
  }

  def migrate(location: Location)
  {
    migrate(location.receiver)
    location match{
      case fl : FieldLocation => require(fields contains fl.field)
      case pl : PredicateLocation => require(predicates contains pl.predicate)
    }

  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t: Term) {
    if (terms contains t)
      return;
    t match {
      case gt: GTerm => super[GTermFactory].migrate(gt)
      case dt: DTerm => super.migrate(dt)
      case pt: PTerm => super.migrate(pt)
      case fa: DomainFunctionApplicationTerm => {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case fa: FunctionApplicationTerm => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case ct: CastTerm => {
        migrate(ct.operand1)
        migrate(ct.newType)
        addTerm(t)
      }
      case fr: FieldReadTerm => {
        require(fields contains fr.location.field)
        migrate(fr.location.receiver)
        addTerm(fr)
      }
      case ut: UnfoldingTerm => {
        require(predicates contains ut.predicate.location.predicate) //Hack - how do we fix this?
        migrate(ut.predicate.location.receiver)
        migrate(ut.term)
        addTerm(ut)
      }
      case ot: OldTerm => {
        migrate(ot.term)
        addTerm(ot)
      }
      case pt: PermTerm => {
        migrate(pt.location.receiver)
        migrate(pt.location)
        addTerm(pt)
      }
      case itet: IfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pTerm)
        migrate(itet.nTerm)
      }

    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(
                                   r: Term,
                                   ff: FunctionFactory,
                                   a: TermSequence,
                                   sourceLocation: SourceLocation,
                                   comment : List[String] = Nil): FunctionApplicationTerm = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate(_))

    (r, a) match {
      case (r: PTerm, a: PTermSequence) => makePFunctionApplicationTerm(r, ff, a,sourceLocation,comment)
      case _ => addTerm(new FunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation,comment))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingTerm(r:PredicatePermissionExpression, t: Term,sourceLocation: SourceLocation,comment : List[String] = Nil): UnfoldingTerm = {
    require(predicates contains r.location.predicate)                                     //Hack
    migrate(r.location.receiver)
    migrate(t)
	
	(r,t) match {
		case (pr:PPredicatePermissionExpression,pt:PTerm) => makePUnfoldingTerm(pr,pt,sourceLocation,comment)
		case _ => addTerm(new UnfoldingTerm(r, t)(sourceLocation,this,comment))
	}
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(t: Term, dt: DataType,sourceLocation: SourceLocation,comment : List[String] = Nil): CastTerm = {
    migrate(dt)
    migrate(t)

    t match {
      case t: PTerm => makePCastTerm(t, dt,sourceLocation,comment)
      case _ => addTerm(new CastTerm(t, dt)(sourceLocation,comment))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(t: Term, f: Field,sourceLocation: SourceLocation,comment : List[String] = Nil): FieldReadTerm = {
    require(fields contains f)
    migrate(t)

    t match {
      case t: PTerm => makePFieldReadTerm(t, f,sourceLocation,comment)
      case _ => addTerm(new FieldReadTerm(new FieldLocation(t, f))(sourceLocation,comment))
    }

  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldTerm(t: Term)(sourceLocation: SourceLocation,comment : List[String] = Nil): OldTerm = {
    migrate(t)
    require(t.programVariables intersect outputProgramVariables isEmpty)
    addTerm(new OldTerm(t)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(
                                         f: DomainFunction,
                                         a: TermSequence,
                                         sourceLocation: SourceLocation,
                                         comment : List[String] = Nil
                                     ): DomainFunctionApplicationTerm = {
    require(domainFunctions contains f)
    a.foreach(migrate(_))

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(f, a,sourceLocation,comment)
      case a: PTermSequence => makePDomainFunctionApplicationTerm(f, a,sourceLocation,comment)
      case a: DTermSequence => makeDDomainFunctionApplicationTerm(f, a,sourceLocation,comment)
      case _ => addTerm(new DomainFunctionApplicationTerm(f, a)(sourceLocation,comment))
    }
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermTerm(location: Term, field: Field)(sourceLocation: SourceLocation,comment : List[String] = Nil): PermTerm = {
    migrate(location)
    require(fields contains field)
    require(location.dataType == referenceType)

    val result = new PermTerm(new FieldLocation(location, field))(sourceLocation,comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermission(percentage: Term,sourceLocation: SourceLocation,comment : List[String] = Nil): Term = {
    val result = new DomainFunctionApplicationTerm(percentagePermission, TermSequence(percentage))(sourceLocation,comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeFullPermission(sourceLocation: SourceLocation,comment : List[String] = Nil): FullPermissionTerm = {
    val result = new FullPermissionTerm()(sourceLocation,comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeNoPermission(sourceLocation: SourceLocation,comment : List[String] = Nil): NoPermissionTerm = {
    val result = new NoPermissionTerm()(sourceLocation,comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeEpsilonPermission(sourceLocation: SourceLocation,comment : List[String] = Nil): EpsilonPermissionTerm = {
    val result = new EpsilonPermissionTerm()(sourceLocation,comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionTerm(t1: Term, t2: Term,sourceLocation: SourceLocation,comment : List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionAddition, TermSequence(t1, t2),sourceLocation,comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionTerm(t1: Term, t2: Term,sourceLocation: SourceLocation,comment : List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionSubtraction, TermSequence(t1, t2),sourceLocation,comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationTerm(t1: Term, t2: Term,sourceLocation: SourceLocation,comment : List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionMultiplication, TermSequence(t1, t2),sourceLocation,comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationTerm(t1: Term, i: Term,sourceLocation: SourceLocation,comment : List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionIntegerMultiplication, TermSequence(t1, i),sourceLocation,comment)

  /////////////////////////////////////////////////////////////////////////
  def makeIfThenElseTerm(c: Term, p: Term, n: Term)(sourceLocation: SourceLocation,comment : List[String] = Nil): IfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc: GTerm, gp: GTerm, gn: GTerm) => makeGIfThenElseTerm(gc, gp, gn,sourceLocation,comment)
      case (dc: DTerm, dp: DTerm, dn: DTerm) => makeDIfThenElseTerm(dc, dp, dn,sourceLocation,comment)
      case (pc: PTerm, pp: PTerm, pn: PTerm) => makePIfThenElseTerm(pc, pp, pn,sourceLocation,comment)
      case _ => addTerm(new IfThenElseTerm(c, p, n)(sourceLocation,comment))
    }
  }
}