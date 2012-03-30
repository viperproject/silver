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
  with TermFactory
{
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrateP(e:PExpression)
  {
    super[PExpressionFactory].migrate(e)
  }

  protected[silAST] def migrate(e:Expression)
  {
    if (expressions contains e)
      return

    e match {
      case ge : GExpression => super[GExpressionFactory].migrate(ge)
      case de : DExpression => super.migrate(de)
      case pe : PExpression => super.migrate(pe)
      case ue : UnaryExpression => {
        migrate(ue.operand1)
      }
      case be : BinaryExpression => {
        migrate(be.operand1)
        migrate(be.operand2)
      }
      case dpe : DomainPredicateExpression => {
        require(domainPredicates contains dpe.predicate)
        dpe.arguments.foreach(migrate(_))
      }
      case ee : EqualityExpression =>
      {
        migrate(ee.term1)
        migrate(ee.term2)
      }
      case ppe : PredicateExpression => {
        require(predicates contains ppe.predicate)
      }
      case pue : UnfoldingExpression => {
        migrate(pue.expression)
        migrate(pue.predicate)
      }
      case qe : QuantifierExpression =>
      {
        require(boundVariables contains qe.variable)
        require(!(boundVariableMap contains qe.variable))
        migrate(qe.expression)
      }
      case pe : PermissionExpression =>
      {
        require(fields contains pe.field)
        migrate(pe.reference)
        migrate(pe.permission)
      }
      case oe : OldExpression =>
      {
        migrate(oe.expression)
      }
    }
    addExpression(e)
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeUnaryExpression(op: UnaryConnective, e1: Expression)(sourceLocation : SourceLocation) : UnaryExpression = {
    migrate(e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(op, e1)(sourceLocation)
      case (e1: PExpression) => makePUnaryExpression(op, e1)(sourceLocation)
      case (e1: DExpression) => makeDUnaryExpression(op, e1)(sourceLocation)
      case _ => addExpression(new UnaryExpression(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeBinaryExpression(op: BinaryConnective, e1: Expression, e2: Expression)(sourceLocation : SourceLocation): BinaryExpression = {
    migrate(e1)
    migrate(e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(op, e1, e2)(sourceLocation)
      case (e1: PExpression, e2: PExpression) => makePBinaryExpression(op, e1, e2)(sourceLocation)
      case (e1: DExpression, e2: DExpression) => makeDBinaryExpression(op, e1, e2)(sourceLocation)
      case _ => addExpression(new BinaryExpression(op, e1, e2)(sourceLocation))
    }
  }


  //////////////////////////////////////////////////////////////////////////
  def makeDomainPredicateExpression(p: DomainPredicate, args: TermSequence)(sourceLocation : SourceLocation): DomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate (_))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(p, a)(sourceLocation)
      case (a: PTermSequence) => makePDomainPredicateExpression(p, a)(sourceLocation)
      case (a: DTermSequence) => makeDDomainPredicateExpression(p, a)(sourceLocation)
      case _ => addExpression(new DomainPredicateExpression(p, args)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePredicateExpression(r: Term, pf: PredicateFactory)(sourceLocation : SourceLocation): PredicateExpression = {
    require(predicates contains pf.pPredicate)
    migrate(r)

    (r) match {
      case (r: PTerm) => makePPredicateExpression(r, pf.pPredicate)(sourceLocation)
      case _ => addExpression(new PredicateExpression(r, pf.pPredicate)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(t1: Term, t2: Term)(sourceLocation : SourceLocation): EqualityExpression = {
    migrate(t1)
    migrate(t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(t1, t2)(sourceLocation)
      case (t1: PTerm, t2: PTerm) => makePEqualityExpression(t1, t2)(sourceLocation)
      case (t1: DTerm, t2: DTerm) => makeDEqualityExpression(t1, t2)(sourceLocation)
      case _ => addExpression(new EqualityExpression(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeOldExpression(e : Expression)(sourceLocation : SourceLocation) : OldExpression = {
    migrate(e)
    require((e.programVariables intersect outputProgramVariables).isEmpty)
    addExpression(OldExpression(e)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeQuantifierExpression(q: Quantifier, v: LogicalVariable, e: Expression)(sourceLocation : SourceLocation): QuantifierExpression = {
    require(boundVariables contains v)
    require(!(boundVariableMap contains v))

    migrate(e)

    e match {
      case e: DExpression => makeDQuantifierExpression(q, v, e)(sourceLocation)
      case _ => {
        val result = addExpression(new QuantifierExpression(q, v, e)(sourceLocation))
        boundVariableMap += v -> result

        result
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePermissionExpression(r: Term, f : Field, p: Term)(sourceLocation : SourceLocation): PermissionExpression = {
    require(fields contains f)
    migrate(r)
    migrate(p)

    addExpression(new PermissionExpression(r, f,p)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(p: PredicateExpression, e: Expression)(sourceLocation : SourceLocation): UnfoldingExpression = {
    migrate(p)
    migrate(e)

    (p, e) match {
      case (p: PPredicateExpression, e: PExpression) => makePUnfoldingExpression(p, e)(sourceLocation)
      case _ => addExpression(new UnfoldingExpression(p, e)(sourceLocation))
    }
  }
}