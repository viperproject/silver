package silAST.expressions

import silAST.domains.DomainPredicate
import silAST.source.SourceLocation
import collection.Set
import collection.mutable.HashSet
import silAST.expressions.util.GTermSequence
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import terms.{GTermFactory, GTerm}
import silAST.programs.NodeFactory


private[silAST] trait GExpressionFactory extends NodeFactory with GTermFactory {
  //////////////////////////////////////////////////////////////////////////
  def makeGUnaryExpression(sourceLocation : SourceLocation, op: UnaryConnective, e1: GExpression): GUnaryExpression = {
    require(expressions contains e1)

    addExpression(new GUnaryExpression(sourceLocation, op, e1))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGDomainPredicateExpression(sourceLocation : SourceLocation, p: DomainPredicate, args: GTermSequence): GDomainPredicateExpression = {
    require(domainPredicates contains p)
    require(args.forall(terms contains _))
    addExpression(new GDomainPredicateExpression(sourceLocation, p, args))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGBinaryExpression(sourceLocation : SourceLocation, op: BinaryConnective, e1: GExpression, e2: GExpression): GBinaryExpression = {
    require(expressions contains e1)
    require(expressions contains e2)

    addExpression(new GBinaryExpression(sourceLocation, op, e1, e2))

  }

  //////////////////////////////////////////////////////////////////////////
  def makeGEqualityExpression(
                               sourceLocation : SourceLocation,
                               t1: GTerm,
                               t2: GTerm
                               ): GEqualityExpression = {
    require(terms contains t1)
    require(terms contains t2)
    addExpression(new GEqualityExpression(sourceLocation, t1, t2))
  }


  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def addExpression[E <: Expression](e: E): E = {
    pExpressions += e
    nodeMap += e.sourceLocation -> e //Overrides sub expressions - always largest in the map
    e
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////

  protected[expressions] val pExpressions = new HashSet[Expression]

  protected[silAST] def expressions: Set[Expression] = pExpressions

  protected[silAST] def domainPredicates: Set[DomainPredicate]

}