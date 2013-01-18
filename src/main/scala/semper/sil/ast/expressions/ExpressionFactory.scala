package semper.sil.ast.expressions

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.symbols.logical.{UnaryConnective, BinaryConnective}
import semper.sil.ast.domains.{DomainFunction, LogicalVariableSubstitutionC, LogicalVariableSubstitution, DomainPredicate}
import terms._
import terms.CastExpression
import terms.DomainFunctionApplicationExpression
import terms.EpsilonPermissionExpression
import terms.FieldLocation
import terms.FieldReadExpression
import terms.FullPermissionExpression
import terms.FunctionApplicationExpression
import terms.IfThenElseExpression
import terms.IntegerLiteralExpression
import terms.LogicalVariableExpression
import terms.NoPermissionExpression
import terms.PermExpression
import terms.PredicateLocation
import terms.ProgramVariableExpression
import util._
import semper.sil.ast.symbols.logical.quantification.{LogicalVariable, Quantifier}
import semper.sil.ast.programs.NodeFactory
import semper.sil.ast.programs.symbols._
import collection.{immutable, mutable}
import semper.sil.ast.types._

trait ExpressionFactory
  extends NodeFactory
  with DataTypeFactory {
  //////////////////////////////////////////////////////////////////////////

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

  protected[sil] def migrate(e: Expression) {
    if (expressions contains e)
      return

    e match {
      case te: TrueExpression => {}
      case fe: FalseExpression => {}
      case ue: UnaryExpression => {
        migrate(ue.operand1)
      }
      case be: BinaryExpression => {
        migrate(be.operand1)
        migrate(be.operand2)
      }
      case dpe: DomainPredicateExpression => {
        require(domainPredicates contains dpe.predicate)
        dpe.arguments.foreach(migrate(_))
      }
      case ee: EqualityExpression => {
        migrate(ee.term1)
        migrate(ee.term2)
      }
      /*      case ppe: PredicateExpression => {
              require(predicates contains ppe.predicate.predicate)
            }*/
      case qe: QuantifierExpression => {
        // TODO: decide how to handle bound variables in migration (Christian Klauser <klauserc@ethz.ch>)
        //require(boundVariables contains qe.variable)
        boundVariables += qe.variable
        require(!(boundVariableMap contains qe.variable))
        migrate(qe.expression)
      }
      case pe: PermissionExpression => {
        pe.location match {
          case fl: FieldLocation => require(fields contains fl.field)
          case pl: PredicateLocation => require(predicates contains pl.predicate)
        }
        migrate(pe.location.receiver)
        migrate(pe.permission)
      }
      case t: LiteralExpression => addExpression(t)
      case fa: DomainFunctionApplicationExpression => {
        require(domainFunctions contains fa.function)
        fa.arguments.foreach(migrate(_))
      }
      case pv: ProgramVariableExpression => {
        require(programVariables contains pv.variable)
      }
      case lv: LogicalVariableExpression => {
        // TODO: Decide how to handle this.
        // I think that bound variables should be migrated automatically. ~~~~ Christian Klauser <klauserc@ethz.ch>
        boundVariables.add(lv.variable)
      }
      case fa: FunctionApplicationExpression => {
        require(functions contains fa.function)
        fa.arguments.foreach(migrate(_))
      }
      case ct: CastExpression => {
        migrate(ct.operand1)
        migrate(ct.newType)
      }
      case fr: FieldReadExpression => {
        require(fields contains fr.location.field)
        migrate(fr.location.receiver)
      }
      case ut: UnfoldingExpression => {
        require(predicates contains ut.predicate.location.predicate) //Hack - how do we fix this?
        migrate(ut.predicate.location.receiver)
        migrate(ut.expression)
      }
      case ot: OldExpression => {
        migrate(ot.expression)
      }
      case pt: PermExpression => {
        migrate(pt.location.receiver)
        migrate(pt.location)
      }
      case itet: IfThenElseExpression => {
        require(itet.condition.dataType == booleanType)
        migrate(itet.condition)
        migrate(itet.pExpression)
        migrate(itet.nExpression)
      }
    }
    addExpression(e)
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeUnaryExpression(op: UnaryConnective, e1: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): UnaryExpression = {
    migrate(e1)

    addExpression(new UnaryExpression(op, e1)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeBinaryExpression(
                            op: BinaryConnective,
                            e1: Expression,
                            e2: Expression,
                            sourceLocation: SourceLocation,
                            comment: List[String] = Nil): BinaryExpression = {
    migrate(e1)
    migrate(e2)

    addExpression(new BinaryExpression(op, e1, e2)(sourceLocation, comment))
  }


  //////////////////////////////////////////////////////////////////////////
  def makeDomainPredicateExpression(
                                     p: DomainPredicate,
                                     args: ExpressionSequence,
                                     sourceLocation: SourceLocation,
                                     comment: List[String] = Nil): DomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate(_))

    addExpression(new DomainPredicateExpression(p, args)(sourceLocation, comment))
  }

  /*
    //////////////////////////////////////////////////////////////////////////
    def makePredicateExpression(r: Expression, pf: PredicateFactory,sourceLocation: SourceLocation,comment : List[String] = Nil): PredicateExpression = {
      require(predicates contains pf.pPredicate)
      migrate(r)

      (r) match {
        case (r: PExpression) => makePPredicateExpression(r, pf.pPredicate,sourceLocation,comment)
        case _ => addExpression(new PredicateExpression(r, pf.pPredicate)(sourceLocation,comment))
      }
    }
    */
  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(t1: Expression, t2: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): EqualityExpression = {
    migrate(t1)
    migrate(t2)

    addExpression(new EqualityExpression(t1, t2)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeOldExpression(e: Expression)(sourceLocation: SourceLocation, comment: List[String] = Nil): OldExpression = {
    migrate(e)
    require((e.programVariables intersect outputProgramVariables).isEmpty)
    addExpression(OldExpression(e)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeQuantifierExpression(
                                q: Quantifier,
                                v: LogicalVariable,
                                e: Expression
                                )(sourceLocation: SourceLocation, comment: List[String] = Nil): QuantifierExpression = {
    require(boundVariables contains v)
    require(!(boundVariableMap contains v))

    migrate(e)

    val result = addExpression(new QuantifierExpression(q, v, e)(sourceLocation, comment))
    boundVariableMap += v -> result

    result
  }

  //////////////////////////////////////////////////////////////////////////
  def makeFieldPermissionExpression(r: Expression, f: Field, p: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): FieldPermissionExpression = {
    require(fields contains f)
    migrate(r)
    migrate(p)

    addExpression(new FieldPermissionExpression(new FieldLocation(r, f), p)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePredicatePermissionExpression(r: Expression, pf: PredicateFactory, p: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): PredicatePermissionExpression = {
    require(predicates contains pf.pPredicate)
    migrate(r)
    migrate(p)

    addExpression(new PredicatePermissionExpression(new PredicateLocation(r, pf.pPredicate), p)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(r: PredicatePermissionExpression, t: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): UnfoldingExpression = {
    require(predicates contains r.location.predicate) //Hack
    migrate(r.location.receiver)
    migrate(t)

    addExpression(new UnfoldingExpression(r, t)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////
  def makeProgramVariableSequence(vs: Seq[ProgramVariable], sourceLocation: SourceLocation, comment: List[String] = Nil): ProgramVariableSequence = {
    require(vs.forall(programVariables contains _))
    val result = new ProgramVariableSequence(vs)(sourceLocation, comment)
    programVariableSequences += result
    result
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

  //////////////////////////////////////////////////////////////////////////
  protected[sil] def addExpression[E <: Expression](e: E): E = {
    pExpressions += e
    nodeMap += e.sourceLocation -> e //Overrides sub expressions - always largest in the map
    e
  }

  /////////////////////////////////////////////////////////////////////////
  protected[sil] def domainFunctions: collection.Set[DomainFunction]

  /////////////////////////////////////////////////////////////////////////
  protected[expressions] val pExpressions = new mutable.HashSet[Expression]

  protected[sil] def functions: collection.Set[Function]

  protected[sil] def programVariables: collection.Set[ProgramVariable]

  protected[sil] def inputProgramVariables: collection.Set[ProgramVariable]

  //included in programVariables
  protected[sil] def outputProgramVariables: collection.Set[ProgramVariable] //included in programVariables

  protected[sil] def fields: collection.Set[Field]

  /////////////////////////////////////////////////////////////////////////
  protected[sil] val boundVariables = new mutable.HashSet[LogicalVariable]

  protected[sil] def expressions: collection.Set[Expression] = pExpressions.toSet

  protected[sil] def domainPredicates: collection.Set[DomainPredicate]

  protected[sil] def predicates: collection.Set[Predicate]

  protected[sil] val programVariableSequences = new mutable.HashSet[ProgramVariableSequence]

  protected[sil] val boundVariableMap = new mutable.HashMap[LogicalVariable, QuantifierExpression]
}