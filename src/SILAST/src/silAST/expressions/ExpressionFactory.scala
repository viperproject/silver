package silAST.expressions

import silAST.source.SourceLocation
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.domains.DomainPredicate
import terms._
import util._
import silAST.symbols.logical.quantification.{BoundVariable, Quantifier}
import silAST.programs.NodeFactory
import silAST.programs.symbols.{Field, PredicateFactory}


trait ExpressionFactory extends NodeFactory with DExpressionFactory with PExpressionFactory with TermFactory {
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeUnaryExpression(sourceLocation : SourceLocation, op: UnaryConnective, e1: Expression): UnaryExpression = {
    require(expressions contains e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sourceLocation, op, e1)
      case (e1: PExpression) => makePUnaryExpression(sourceLocation, op, e1)
      case (e1: DExpression) => makeDUnaryExpression(sourceLocation, op, e1)
      case _ => addExpression(new UnaryExpression(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeBinaryExpression(sourceLocation : SourceLocation, op: BinaryConnective, e1: Expression, e2: Expression): BinaryExpression = {
    require(expressions contains e1)
    require(expressions contains e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sourceLocation, op, e1, e2)
      case (e1: PExpression, e2: PExpression) => makePBinaryExpression(sourceLocation, op, e1, e2)
      case (e1: DExpression, e2: DExpression) => makeDBinaryExpression(sourceLocation, op, e1, e2)
      case _ => addExpression(new BinaryExpression(op, e1, e2)(sourceLocation))
    }
  }


  //////////////////////////////////////////////////////////////////////////
  def makeDomainPredicateExpression(sourceLocation : SourceLocation, p: DomainPredicate, args: TermSequence): DomainPredicateExpression = {
    require(domainPredicates contains p)
    require(args.forall(terms contains _))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sourceLocation, p, a)
      case (a: PTermSequence) => makePDomainPredicateExpression(sourceLocation, p, a)
      case (a: DTermSequence) => makeDDomainPredicateExpression(sourceLocation, p, a)
      case _ => addExpression(new DomainPredicateExpression(p, args)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePredicateExpression(sourceLocation : SourceLocation, r: Term, pf: PredicateFactory): PredicateExpression = {
    require(predicates contains pf.pPredicate)
    require(terms contains r)

    (r) match {
      case (r: PTerm) => makePPredicateExpression(sourceLocation, r, pf.pPredicate)
      case _ => addExpression(new PredicateExpression(r, pf.pPredicate)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(sourceLocation : SourceLocation, t1: Term, t2: Term): EqualityExpression = {
    require(terms contains t1)
    require(terms contains t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sourceLocation, t1, t2)
      case (t1: PTerm, t2: PTerm) => makePEqualityExpression(sourceLocation, t1, t2)
      case (t1: DTerm, t2: DTerm) => makeDEqualityExpression(sourceLocation, t1, t2)
      case _ => addExpression(new EqualityExpression(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeQuantifierExpression(sourceLocation : SourceLocation, q: Quantifier, v: BoundVariable, e: Expression): QuantifierExpression = {
    require(boundVariables contains v)
    require(!(boundVariableMap contains v))

    require(expressions contains e)

    e match {
      case e: DExpression => makeDQuantifierExpression(sourceLocation, q, v, e)
      case _ => {
        val result = addExpression(new QuantifierExpression(q, v, e)(sourceLocation))
        boundVariableMap += v -> result

        result
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePermissionExpression(sourceLocation : SourceLocation, r: Term, f : Field, p: Term): PermissionExpression = {
    require(terms contains r)
    require(terms contains p)
    require(fields contains f)

    addExpression(new PermissionExpression(r, f,p)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(sourceLocation : SourceLocation, p: PredicateExpression, e: Expression): UnfoldingExpression = {
    require(expressions contains p)
    require(expressions contains e)

    (p, e) match {
      case (p: PPredicateExpression, e: PExpression) => makePUnfoldingExpression(sourceLocation, p, e)
      case _ => addExpression(new UnfoldingExpression(p, e)(sourceLocation))
    }
  }
}