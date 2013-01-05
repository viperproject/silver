package semper.sil.ast.expressions.terms

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.programs.NodeFactory
import semper.sil.ast.expressions.util._
import semper.sil.ast.types._
import collection.immutable
import collection.mutable
import semper.sil.ast.programs.symbols.{Function, Predicate, ProgramVariable, FunctionFactory, Field}
import semper.sil.ast.symbols.logical.quantification.LogicalVariable
import semper.sil.ast.domains.{LogicalVariableSubstitutionC, LogicalVariableSubstitution, DomainFunction}
import semper.sil.ast.expressions.{Expression, PredicatePermissionExpression, ProgramVariableSubstitutionC, ProgramVariableSubstitution}

protected[sil] trait TermFactory
  extends NodeFactory
  with DataTypeFactory {
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
  def migrate(location: Location) {
    migrate(location.receiver)
    location match {
      case fl: FieldLocation => require(fields contains fl.field)
      case pl: PredicateLocation => require(predicates contains pl.predicate)
    }

  }

  /////////////////////////////////////////////////////////////////////////
  protected[sil] def migrate(t: Term) {
    if (terms contains t)
      return
    t match {
      case t: LiteralTerm => addTerm(t)
      case fa: DomainFunctionApplicationTerm => {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addTerm(fa)
      }
      case pv: ProgramVariableTerm => {
        require(programVariables contains pv.variable)
        addTerm(pv)
      }
      case lv: LogicalVariableTerm => {
        // TODO: Decide how to handle this.
        // I think that bound variables should be migrated automatically. ~~~~ Christian Klauser <klauserc@ethz.ch>
        boundVariables.add(lv.variable)
        addTerm(lv)
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
  def validBoundVariableName(name: String): Boolean =
    name != "this"

  /////////////////////////////////////////////////////////////////////////
  def makeBoundVariable(name: String, dataType: DataType, sourceLocation: SourceLocation, comment: List[String] = Nil): LogicalVariable = {
    require(dataTypes contains dataType)
    require(validBoundVariableName(name))
    val result: LogicalVariable = new LogicalVariable(name, dataType)(sourceLocation, comment)
    boundVariables += result
    result
  }

  /////////////////////////////////////////////////////////////////////////
  def makeBoundVariableTerm(v: LogicalVariable, sourceLocation: SourceLocation, comment: List[String] = Nil): LogicalVariableTerm = {
    require(boundVariables contains v)
    addTerm(new LogicalVariableTerm(v)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeIntegerLiteralTerm(v: BigInt, sourceLocation: SourceLocation, comment: List[String] = Nil): IntegerLiteralTerm = {
    addTerm(new IntegerLiteralTerm(v)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationTerm(
                                   r: Term,
                                   ff: FunctionFactory,
                                   a: TermSequence,
                                   sourceLocation: SourceLocation,
                                   comment: List[String] = Nil): FunctionApplicationTerm = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate(_))

    addTerm(new FunctionApplicationTerm(r, ff.pFunction, a)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableTerm(v: ProgramVariable, sourceLocation: SourceLocation, comment: List[String] = Nil): ProgramVariableTerm = {
    if (!(programVariables contains v)) {
      System.out.println("PTF : " + programVariables.mkString(","))
    }
    require(programVariables contains v)
    addTerm(new ProgramVariableTerm(v)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingTerm(r: PredicatePermissionExpression, t: Term, sourceLocation: SourceLocation, comment: List[String] = Nil): UnfoldingTerm = {
    require(predicates contains r.location.predicate) //Hack
    migrate(r.location.receiver)
    migrate(t)

    addTerm(new UnfoldingTerm(r, t)(sourceLocation, this, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastTerm(t: Term, dt: DataType, sourceLocation: SourceLocation, comment: List[String] = Nil): CastTerm = {
    migrate(dt)
    migrate(t)

    addTerm(new CastTerm(t, dt)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadTerm(t: Term, f: Field, sourceLocation: SourceLocation, comment: List[String] = Nil): FieldReadTerm = {
    require(fields contains f)
    migrate(t)

    addTerm(new FieldReadTerm(new FieldLocation(t, f))(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldTerm(t: Term)(sourceLocation: SourceLocation, comment: List[String] = Nil): OldTerm = {
    migrate(t)
    require(t.programVariables intersect outputProgramVariables isEmpty)
    addTerm(new OldTerm(t)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationTerm(
                                         f: DomainFunction,
                                         a: TermSequence,
                                         sourceLocation: SourceLocation,
                                         comment: List[String] = Nil
                                         ): DomainFunctionApplicationTerm = {
    assert(domainFunctions contains f)
    a.foreach(migrate(_))

    addTerm(new DomainFunctionApplicationTerm(f, a)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermTerm(location: Term, field: Field)(sourceLocation: SourceLocation, comment: List[String] = Nil): PermTerm = {
    migrate(location)
    require(fields contains field)
    require(location.dataType == referenceType)

    val result = new PermTerm(new FieldLocation(location, field))(sourceLocation, comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermission(percentage: Term, sourceLocation: SourceLocation, comment: List[String] = Nil): Term = {
    makeDomainFunctionApplicationTerm(percentagePermission, TermSequence(percentage), sourceLocation, comment)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeFullPermission(sourceLocation: SourceLocation, comment: List[String] = Nil): FullPermissionTerm = {
    val result = new FullPermissionTerm()(sourceLocation, comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeNoPermission(sourceLocation: SourceLocation, comment: List[String] = Nil): NoPermissionTerm = {
    val result = new NoPermissionTerm()(sourceLocation, comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeEpsilonPermission(sourceLocation: SourceLocation, comment: List[String] = Nil): EpsilonPermissionTerm = {
    val result = new EpsilonPermissionTerm()(sourceLocation, comment)
    addTerm(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionTerm(t1: Term, t2: Term, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionAddition, TermSequence(t1, t2), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionTerm(t1: Term, t2: Term, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionSubtraction, TermSequence(t1, t2), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationTerm(t1: Term, t2: Term, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionMultiplication, TermSequence(t1, t2), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationTerm(t1: Term, i: Term, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationTerm(permissionIntegerMultiplication, TermSequence(t1, i), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////
  def makeIfThenElseTerm(c: Term, p: Term, n: Term)(sourceLocation: SourceLocation, comment: List[String] = Nil): IfThenElseTerm = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    addTerm(new IfThenElseTerm(c, p, n)(sourceLocation, comment))
  }

  protected[sil] def addTerm[T <: Term](t: T): T = {
    terms += t
    t
  }

  //////////////////////////////////////////////////////////////////////////
  protected[sil] def addExpression[E <: Expression](e: E): E = {
    pExpressions += e
    nodeMap += e.sourceLocation -> e //Overrides sub expressions - always largest in the map
    e
  }

  /////////////////////////////////////////////////////////////////////////
  protected val terms = new mutable.HashSet[Term]

  protected[sil] def domainFunctions: collection.Set[DomainFunction]

  /////////////////////////////////////////////////////////////////////////
  protected[expressions] val pExpressions = new mutable.HashSet[Expression]

  protected[sil] def functions: collection.Set[Function]

  protected[sil] def programVariables: collection.Set[ProgramVariable]

  protected[sil] def inputProgramVariables: collection.Set[ProgramVariable]

  //included in programVariables
  protected[sil] def outputProgramVariables: collection.Set[ProgramVariable] //included in programVariables

  protected[sil] def fields: collection.Set[Field]

  protected[sil] def predicates: collection.Set[Predicate]

  /////////////////////////////////////////////////////////////////////////
  protected[sil] val boundVariables = new mutable.HashSet[LogicalVariable]
}