package semper.sil.ast.expressions

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.symbols.logical.{UnaryConnective, BinaryConnective}
import semper.sil.ast.domains.DomainPredicate
import terms._
import terms.FieldLocation
import terms.PredicateLocation
import util._
import semper.sil.ast.symbols.logical.quantification.{LogicalVariable, Quantifier}
import semper.sil.ast.programs.NodeFactory
import semper.sil.ast.programs.symbols._
import collection.mutable

trait ExpressionFactory
  extends NodeFactory
  with TermFactory {
  //////////////////////////////////////////////////////////////////////////

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
      case pue: UnfoldingExpression => {
        migrate(pue.location)
        migrate(pue.expression)
      }
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
      case oe: OldExpression => {
        migrate(oe.expression)
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
                                     args: TermSequence,
                                     sourceLocation: SourceLocation,
                                     comment: List[String] = Nil): DomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate(_))

    addExpression(new DomainPredicateExpression(p, args)(sourceLocation, comment))
  }

  /*
    //////////////////////////////////////////////////////////////////////////
    def makePredicateExpression(r: Term, pf: PredicateFactory,sourceLocation: SourceLocation,comment : List[String] = Nil): PredicateExpression = {
      require(predicates contains pf.pPredicate)
      migrate(r)

      (r) match {
        case (r: PTerm) => makePPredicateExpression(r, pf.pPredicate,sourceLocation,comment)
        case _ => addExpression(new PredicateExpression(r, pf.pPredicate)(sourceLocation,comment))
      }
    }
    */
  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(t1: Term, t2: Term, sourceLocation: SourceLocation, comment: List[String] = Nil): EqualityExpression = {
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
  def makeFieldPermissionExpression(r: Term, f: Field, p: Term, sourceLocation: SourceLocation, comment: List[String] = Nil): FieldPermissionExpression = {
    require(fields contains f)
    migrate(r)
    migrate(p)

    addExpression(new FieldPermissionExpression(new FieldLocation(r, f), p)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePredicatePermissionExpression(r: Term, pf: PredicateFactory, p: Term, sourceLocation: SourceLocation, comment: List[String] = Nil): PredicatePermissionExpression = {
    require(predicates contains pf.pPredicate)
    migrate(r)
    migrate(p)

    addExpression(new PredicatePermissionExpression(new PredicateLocation(r, pf.pPredicate), p)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(r: PredicatePermissionExpression, e: Expression, sourceLocation: SourceLocation, comment: List[String] = Nil): UnfoldingExpression = {
    migrate(r)
    migrate(e)

    addExpression(new UnfoldingExpression(r, e)(sourceLocation, comment))
  }

  //////////////////////////////////////////////////////////////////
  def makeProgramVariableSequence(vs: Seq[ProgramVariable], sourceLocation: SourceLocation, comment: List[String] = Nil): ProgramVariableSequence = {
    require(vs.forall(programVariables contains _))
    val result = new ProgramVariableSequence(vs)(sourceLocation, comment)
    programVariableSequences += result
    result
  }

  protected[sil] def expressions: collection.Set[Expression] = pExpressions.toSet

  protected[sil] def domainPredicates: collection.Set[DomainPredicate]

  protected[sil] def predicates: collection.Set[Predicate]

  protected[sil] val programVariableSequences = new mutable.HashSet[ProgramVariableSequence]

  protected[sil] val boundVariableMap = new mutable.HashMap[LogicalVariable, QuantifierExpression]
}