package silAST.expressions

import silAST.source.SourceLocation
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.domains.DomainPredicate
import terms._
import util._
import silAST.symbols.logical.quantification.{LogicalVariable, Quantifier}
import silAST.programs.NodeFactory
import silAST.programs.symbols.{Field, PredicateFactory}


trait ExpressionFactory
  extends NodeFactory
  with DExpressionFactory
  with PExpressionFactory
  with GExpressionFactory
  with TermFactory {
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateP(e: PExpression) {
    super[PExpressionFactory].migrate(e)
  }

  protected[silAST] def migrate(e: Expression) {
    if (expressions contains e)
      return

    e match {
      case ge: GExpression => super[GExpressionFactory].migrate(ge)
      case de: DExpression => super.migrate(de)
      case pe: PExpression => super.migrate(pe)
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
        require(boundVariables contains qe.variable)
        require(!(boundVariableMap contains qe.variable))
        migrate(qe.expression)
      }
      case pe: PermissionExpression => {
        pe.location match {
          case fl : FieldLocation     => require(fields contains fl.field)
          case pl : PredicateLocation => require(predicates contains pl.predicate)
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
  def makeUnaryExpression(op: UnaryConnective, e1: Expression,sourceLocation: SourceLocation,comment :List[String] = Nil): UnaryExpression = {
    migrate(e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(op, e1,sourceLocation,comment)
      case (e1: PExpression) => makePUnaryExpression(op, e1,sourceLocation,comment)
      case (e1: DExpression) => makeDUnaryExpression(op, e1,sourceLocation,comment)
      case _ => addExpression(new UnaryExpression(op, e1)(sourceLocation,comment))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeBinaryExpression(
                            op: BinaryConnective,
                            e1: Expression,
                            e2: Expression,
                            sourceLocation: SourceLocation,
                            comment : List[String] = Nil): BinaryExpression = {
    migrate(e1)
    migrate(e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(op, e1, e2,sourceLocation,comment)
      case (e1: PExpression, e2: PExpression) => makePBinaryExpression(op, e1, e2,sourceLocation,comment)
      case (e1: DExpression, e2: DExpression) => makeDBinaryExpression(op, e1, e2,sourceLocation,comment)
      case _ => addExpression(new BinaryExpression(op, e1, e2)(sourceLocation,comment))
    }
  }


  //////////////////////////////////////////////////////////////////////////
  def makeDomainPredicateExpression(
                                     p: DomainPredicate,
                                     args: TermSequence,
                                     sourceLocation: SourceLocation,
                                     comment : List[String] = Nil): DomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate(_))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(p, a,sourceLocation,comment)
      case (a: PTermSequence) => makePDomainPredicateExpression(p, a,sourceLocation,comment)
      case (a: DTermSequence) => makeDDomainPredicateExpression(p, a,sourceLocation,comment)
      case _ => addExpression(new DomainPredicateExpression(p, args)(sourceLocation,comment))
    }
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
  def makeEqualityExpression(t1: Term, t2: Term,sourceLocation: SourceLocation,comment : List[String] = Nil): EqualityExpression = {
    migrate(t1)
    migrate(t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(t1, t2,sourceLocation,comment)
      case (t1: PTerm, t2: PTerm) => makePEqualityExpression(t1, t2,sourceLocation,comment)
      case (t1: DTerm, t2: DTerm) => makeDEqualityExpression(t1, t2,sourceLocation,comment)
      case _ => addExpression(new EqualityExpression(t1, t2)(sourceLocation,comment))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeOldExpression(e: Expression)(sourceLocation: SourceLocation,comment : List[String] = Nil): OldExpression = {
    migrate(e)
    require((e.programVariables intersect outputProgramVariables).isEmpty)
    addExpression(OldExpression(e)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeQuantifierExpression(
        q: Quantifier,
        v: LogicalVariable,
        e: Expression
      )(sourceLocation: SourceLocation,comment : List[String] = Nil) : QuantifierExpression =
  {
    require(boundVariables contains v)
    require(!(boundVariableMap contains v))

    migrate(e)

    e match {
      case e: DExpression => makeDQuantifierExpression(q, v, e,sourceLocation,comment)
      case _ => {
        val result = addExpression(new QuantifierExpression(q, v, e)(sourceLocation,comment))
        boundVariableMap += v -> result

        result
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeFieldPermissionExpression(r: Term, f: Field, p: Term,sourceLocation: SourceLocation,comment : List[String] = Nil): FieldPermissionExpression = {
    require(fields contains f)
    migrate(r)
    migrate(p)

    addExpression(new FieldPermissionExpression(new FieldLocation(r, f), p)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePredicatePermissionExpression(r: Term, pf: PredicateFactory, p: Term,sourceLocation: SourceLocation,comment : List[String] = Nil): PredicatePermissionExpression = {
    require(predicates contains pf.pPredicate)
    migrate(r)
    migrate(p)

    addExpression(new PredicatePermissionExpression(new PredicateLocation(r, pf.pPredicate), p)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(r: PredicatePermissionExpression, e: Expression,sourceLocation: SourceLocation,comment : List[String] = Nil): UnfoldingExpression = {
    migrate(r)
    migrate(e)

    (r,e) match{
      case (pr:PPredicatePermissionExpression,pe:PExpression) => makePUnfoldingExpression(pr,pe,sourceLocation,comment)
      case _ => addExpression(new UnfoldingExpression(r, e)(sourceLocation,comment))
    }

  }
}