package silAST.expressions

import collection.Set
import silAST.source.SourceLocation
import silAST.domains.DomainPredicate
import terms.{PTermFactory, PTerm, GTerm}
import util.{GTermSequence, PTermSequence}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.programs.NodeFactory
import silAST.programs.symbols.Predicate


trait PExpressionFactory extends NodeFactory with GExpressionFactory with PTermFactory {
  //////////////////////////////////////////////////////////////////////////
  def makePDomainPredicateExpression(sourceLocation : SourceLocation, p: DomainPredicate, args: PTermSequence): PDomainPredicateExpression = {
    require(domainPredicates contains p)
    require(args.forall(terms contains _))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sourceLocation, p, a)
      case _ => addExpression(new PDomainPredicateExpressionC(p, args)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePPredicateExpression(sourceLocation : SourceLocation, r: PTerm, p: Predicate): PPredicateExpression = {
    require(predicates contains p)
    require(terms contains r)

    addExpression(new PPredicateExpression(r, p)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnaryExpression(sourceLocation : SourceLocation, op: UnaryConnective, e1: PExpression): PUnaryExpression = {
    require(expressions contains e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sourceLocation, op, e1)
      case _ => addExpression(new PUnaryExpressionC(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePBinaryExpression(sourceLocation : SourceLocation, op: BinaryConnective, e1: PExpression, e2: PExpression): PBinaryExpression = {
    require(expressions contains e1)
    require(expressions contains e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sourceLocation, op, e1, e2)
      case _ => addExpression(new PBinaryExpressionC(op, e1, e2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePEqualityExpression(sourceLocation : SourceLocation, t1: PTerm, t2: PTerm): PEqualityExpression = {
    require(terms contains t1)
    require(terms contains t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sourceLocation, t1, t2)
      case _ => addExpression(new PEqualityExpressionC(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingExpression(sourceLocation : SourceLocation, p: PPredicateExpression, e: PExpression): UnfoldingExpression = {
    require(expressions contains p)
    require(expressions contains e)

    addExpression(new PUnfoldingExpression(p, e)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def predicates: Set[Predicate]
}