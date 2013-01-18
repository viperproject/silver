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

protected[sil] trait ExpressionFactory
  extends NodeFactory
  with DataTypeFactory {
  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableSubstitution(subs: immutable.Set[(ProgramVariable, Expression)]): ProgramVariableSubstitution = {
    subs.foreach(kv => migrate(kv._2))
    new ProgramVariableSubstitutionC(subs, Set())
  }

  /////////////////////////////////////////////////////////////////////////
  def makeLogicalVariableSubstitution(subs: immutable.Set[(LogicalVariable, Expression)]): LogicalVariableSubstitution = {
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
  protected[sil] def migrate(t: Expression) {
    if (terms contains t)
      return
    t match {
      case t: LiteralExpression => addExpression(t)
      case fa: DomainFunctionApplicationExpression => {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addExpression(fa)
      }
      case pv: ProgramVariableExpression => {
        require(programVariables contains pv.variable)
        addExpression(pv)
      }
      case lv: LogicalVariableExpression => {
        // TODO: Decide how to handle this.
        // I think that bound variables should be migrated automatically. ~~~~ Christian Klauser <klauserc@ethz.ch>
        boundVariables.add(lv.variable)
        addExpression(lv)
      }
      case fa: FunctionApplicationExpression => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrate(_))
        addExpression(fa)
      }
      case ct: CastExpression => {
        migrate(ct.operand1)
        migrate(ct.newType)
        addExpression(t)
      }
      case fr: FieldReadExpression => {
        require(fields contains fr.location.field)
        migrate(fr.location.receiver)
        addExpression(fr)
      }
      case ut: UnfoldingExpression => {
        require(predicates contains ut.predicate.location.predicate) //Hack - how do we fix this?
        migrate(ut.predicate.location.receiver)
        migrate(ut.term)
        addExpression(ut)
      }
      case ot: OldExpression => {
        migrate(ot.term)
        addExpression(ot)
      }
      case pt: PermExpression => {
        migrate(pt.location.receiver)
        migrate(pt.location)
        addExpression(pt)
      }
      case itet: IfThenElseExpression => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pExpression)
        migrate(itet.nExpression)
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
  def makeBoundVariableExpression(v: LogicalVariable, sourceLocation: SourceLocation, comment: List[String] = Nil): LogicalVariableExpression = {
    require(boundVariables contains v)
    addExpression(new LogicalVariableExpression(v)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeIntegerLiteralExpression(v: BigInt, sourceLocation: SourceLocation, comment: List[String] = Nil): IntegerLiteralExpression = {
    addExpression(new IntegerLiteralExpression(v)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFunctionApplicationExpression(
                                   r: Expression,
                                   ff: FunctionFactory,
                                   a: ExpressionSequence,
                                   sourceLocation: SourceLocation,
                                   comment: List[String] = Nil): FunctionApplicationExpression = {
    migrate(r)
    require(functions contains ff.pFunction)
    a.foreach(migrate(_))

    addExpression(new FunctionApplicationExpression(r, ff.pFunction, a)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeProgramVariableExpression(v: ProgramVariable, sourceLocation: SourceLocation, comment: List[String] = Nil): ProgramVariableExpression = {
    if (!(programVariables contains v)) {
      System.out.println("PTF : " + programVariables.mkString(","))
    }
    require(programVariables contains v)
    addExpression(new ProgramVariableExpression(v)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(r: PredicatePermissionExpression, t: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): UnfoldingExpression = {
    require(predicates contains r.location.predicate) //Hack
    migrate(r.location.receiver)
    migrate(t)

    addExpression(new UnfoldingExpression(r, t)(sourceLocation, this, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeCastExpression(t: Expression, dt: DataType, sourceLocation: SourceLocation, comment: List[String] = Nil): CastExpression = {
    migrate(dt)
    migrate(t)

    addExpression(new CastExpression(t, dt)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeFieldReadExpression(t: Expression, f: Field, sourceLocation: SourceLocation, comment: List[String] = Nil): FieldReadExpression = {
    require(fields contains f)
    migrate(t)

    addExpression(new FieldReadExpression(new FieldLocation(t, f))(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeOldExpression(t: Expression)(sourceLocation: SourceLocation, comment: List[String] = Nil): OldExpression = {
    migrate(t)
    require(t.programVariables intersect outputProgramVariables isEmpty)
    addExpression(new OldExpression(t)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////
  def makeDomainFunctionApplicationExpression(
                                         f: DomainFunction,
                                         a: ExpressionSequence,
                                         sourceLocation: SourceLocation,
                                         comment: List[String] = Nil
                                         ): DomainFunctionApplicationExpression = {
    assert(domainFunctions contains f)
    a.foreach(migrate(_))

    addExpression(new DomainFunctionApplicationExpression(f, a)(sourceLocation, comment))
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermExpression(location: Expression, field: Field)(sourceLocation: SourceLocation, comment: List[String] = Nil): PermExpression = {
    migrate(location)
    require(fields contains field)
    require(location.dataType == referenceType)

    val result = new PermExpression(new FieldLocation(location, field))(sourceLocation, comment)
    addExpression(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePercentagePermission(percentage: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): Expression = {
    makeDomainFunctionApplicationExpression(percentagePermission, ExpressionSequence(percentage), sourceLocation, comment)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeFullPermission(sourceLocation: SourceLocation, comment: List[String] = Nil): FullPermissionExpression = {
    val result = new FullPermissionExpression()(sourceLocation, comment)
    addExpression(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeNoPermission(sourceLocation: SourceLocation, comment: List[String] = Nil): NoPermissionExpression = {
    val result = new NoPermissionExpression()(sourceLocation, comment)
    addExpression(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makeEpsilonPermission(sourceLocation: SourceLocation, comment: List[String] = Nil): EpsilonPermissionExpression = {
    val result = new EpsilonPermissionExpression()(sourceLocation, comment)
    addExpression(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionAdditionExpression(t1: Expression, t2: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationExpression(permissionAddition, ExpressionSequence(t1, t2), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionSubtractionExpression(t1: Expression, t2: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationExpression(permissionSubtraction, ExpressionSequence(t1, t2), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionMultiplicationExpression(t1: Expression, t2: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationExpression(permissionMultiplication, ExpressionSequence(t1, t2), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////////////////
  def makePermissionIntegerMultiplicationExpression(t1: Expression, i: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil) =
    makeDomainFunctionApplicationExpression(permissionIntegerMultiplication, ExpressionSequence(t1, i), sourceLocation, comment)

  /////////////////////////////////////////////////////////////////////////
  def makeIfThenElseExpression(c: Expression, p: Expression, n: Expression)(sourceLocation: SourceLocation, comment: List[String] = Nil): IfThenElseExpression = {
    migrate(c)
    migrate(p)
    migrate(n)
    require(c.dataType == booleanType)
    addExpression(new IfThenElseExpression(c, p, n)(sourceLocation, comment))
  }

  protected[sil] def addExpression[T <: Expression](t: T): T = {
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
  protected val terms = new mutable.HashSet[Expression]

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