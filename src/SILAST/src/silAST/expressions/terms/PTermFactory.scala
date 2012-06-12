package silAST.expressions.terms

import silAST.source.SourceLocation

import silAST.programs.NodeFactory
import silAST.expressions.util.{PTermSequence, GTermSequence}
import silAST.programs.symbols._
import silAST.types.{booleanType, DataTypeFactory, DataType}
import collection.{immutable, Set}
import silAST.symbols.logical.quantification.LogicalVariable
import silAST.domains._
import silAST.expressions._
import collection.mutable.HashSet

protected[silAST] trait PTermFactory
  extends NodeFactory
  with GTermFactory
  with DataTypeFactory
{
  def makePProgramVariableSubstitution(subs: immutable.Set[(ProgramVariable, PTerm)]): PProgramVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new PProgramVariableSubstitutionC(subs, immutable.Set[(LogicalVariable, LogicalVariable)]())
  }

  /////////////////////////////////////////////////////////////////////////
  def makePLogicalVariableSubstitution(subs: immutable.Set[(LogicalVariable, PTerm)]): PLogicalVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new PLogicalVariableSubstitutionC(Set(), subs)
  }

  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(l : PLocation) {
    migrate(l.receiver)

    l match {
      case pl : PPredicateLocation => require (predicates contains pl.predicate)
      case pl : PFieldLocation     => require (fields     contains pl.field)
    }
  }
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migratePPredicatePermissionExpression(e: PPredicatePermissionExpression) {
    migrate(e.location)
    migrate(e.permission)
  }
  /////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(t: PTerm) {
    if (terms contains t)
      return;
    t match {
      case gt: GTerm => super.migrate(gt)
      case pv: ProgramVariableTerm => {
        require(programVariables contains pv.variable)
        addTerm(pv)
      }
      case fa: PFunctionApplicationTerm => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case dfa: PDomainFunctionApplicationTerm => {
        dfa.arguments.foreach(migrate(_))
        require(domainFunctions contains dfa.function)
        addTerm(dfa)
      }
      case put: PUnfoldingTerm => {
        migratePPredicatePermissionExpression(put.predicate)
        migrate(put.term)
        addTerm(put)
      }
      case ct: PCastTerm => {
        migrate(ct.operand1)
        migrate(ct.newType)
        addTerm(t)
      }
      case fr: PFieldReadTerm => {
        require(fields contains fr.location.field)
        migrate(fr.location.receiver)
        addTerm(fr)
      }
      case itet: PIfThenElseTerm => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pTerm)
        migrate(itet.nTerm)
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePFieldPermissionExpression(r: PTerm, f: Field, p: PTerm,sourceLocation: SourceLocation,comment : List[String] = Nil): PFieldPermissionExpression = {
    require(fields contains f)
    migrate(r)
    migrate(p)

    addExpression(new PFieldPermissionExpression(new PFieldLocation(r, f), p)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePPredicatePermissionExpression(r: PTerm, pf: PredicateFactory, p: PTerm,sourceLocation: SourceLocation,comment : List[String] = Nil): PPredicatePermissionExpression = {
    require(predicates contains pf.pPredicate)
    migrate(r)
    migrate(p)

    addExpression(new PPredicatePermissionExpression(new PPredicateLocation(r, pf.pPredicate), p)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(v: ProgramVariable,sourceLocation: SourceLocation,comment : List[String] = Nil): ProgramVariableTerm = {
    if (!(programVariables contains v)) {
      System.out.println("PTF : " + programVariables.mkString(","))
    }
    require(programVariables contains v)
    addTerm(new ProgramVariableTerm(v)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFunctionApplicationTerm(
                                    r: PTerm,
                                    ff: FunctionFactory,
                                    a: PTermSequence,
                                    sourceLocation: SourceLocation,
                                    comment : List[String] = Nil): PFunctionApplicationTerm = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate(_))

    addTerm(new PFunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePCastTerm(t: PTerm, dt: DataType,sourceLocation: SourceLocation,comment : List[String] = Nil): PCastTerm = {
    migrate(t)
    migrate(dt)

    addTerm(new PCastTerm(t, dt)(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePFieldReadTerm(t: PTerm, f: Field,sourceLocation: SourceLocation,comment : List[String] = Nil): PFieldReadTerm = {
    migrate(t)
    require(fields contains f)

    addTerm(new PFieldReadTerm(new PFieldLocation(t, f))(sourceLocation,comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makePDomainFunctionApplicationTerm(
                                          f: DomainFunction,
                                          a: PTermSequence,
                                          sourceLocation:  SourceLocation,
                                          comment : List[String] = Nil): PDomainFunctionApplicationTerm = {
    a.foreach(migrate(_))
    require(domainFunctions contains f)

    a match {
      case a: GTermSequence => makeGDomainFunctionApplicationTerm(f, a,sourceLocation,comment)
      case _ => addTerm(new PDomainFunctionApplicationTermC(f, a)(sourceLocation,comment))
    }
  }

  /////////////////////////////////////////////////////////////////////////
  def makePIfThenElseTerm(c: PTerm, p: PTerm, n: PTerm,sourceLocation: SourceLocation,comment : List[String] = Nil): PIfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    (c, p, n) match {
      case (gc: GTerm, gp: GTerm, gn: GTerm) => makeGIfThenElseTerm(gc, gp, gn,sourceLocation,comment)
      case _ => addTerm(new PIfThenElseTermC(c, p, n)(sourceLocation,comment))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingTerm(r:PPredicatePermissionExpression, t: PTerm,sourceLocation: SourceLocation,comment : List[String] = Nil): PUnfoldingTerm = {
    require(predicates contains r.location.predicate)                                     //Hack
    migrate(r.location.receiver)
    migrate(t)

    addTerm(new PUnfoldingTerm(r, t)(sourceLocation,this,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def addExpression[E <: Expression](e: E): E = {
    pExpressions += e
    nodeMap += e.sourceLocation -> e //Overrides sub expressions - always largest in the map
    e
  }

  /////////////////////////////////////////////////////////////////////////
  protected[expressions] val pExpressions = new HashSet[Expression]

  protected[silAST] def functions: Set[Function]

  protected[silAST] def programVariables: collection.Set[ProgramVariable]

  protected[silAST] def inputProgramVariables: collection.Set[ProgramVariable] //included in programVariables
  protected[silAST] def outputProgramVariables: collection.Set[ProgramVariable] //included in programVariables

  protected[silAST] def fields: Set[Field]

  protected[silAST] def predicates: Set[Predicate]
}