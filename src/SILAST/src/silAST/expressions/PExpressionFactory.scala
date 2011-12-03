package silAST.expressions

import collection.mutable.HashMap
import silAST.source.SourceLocation
import silAST.domains.DomainPredicate
import terms.{PTermFactory, PTerm, GTerm}
import util.{GTermSequence, PTermSequence}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.programs.NodeFactory
import silAST.programs.symbols.Predicate


trait PExpressionFactory extends NodeFactory with GExpressionFactory with PTermFactory
{
  //////////////////////////////////////////////////////////////////////////
  def makePDomainPredicateExpression(sl: SourceLocation,p : DomainPredicate, args : PTermSequence): PDomainPredicateExpression =
  {
    require(domainPredicates(p.name) == p)
    require(termSequences.contains(args))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sl,p,a)
      case _ =>  addExpression ( new PDomainPredicateExpressionC(sl,p,args))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePPredicateExpression(sl: SourceLocation, r : PTerm,p : Predicate): PPredicateExpression =
  {
    require(predicates(p.name) == p)
    require(terms.contains(r))

    addExpression ( new PPredicateExpression(sl,r,p))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnaryExpression(sl: SourceLocation,op:UnaryConnective,e1: PExpression): PUnaryExpression = {
    require(expressions.contains(e1))

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sl,op,e1)
      case _ =>  addExpression ( new PUnaryExpressionC(sl, op,e1) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePBinaryExpression(sl: SourceLocation,op:BinaryConnective,e1: PExpression, e2:PExpression): PBinaryExpression = {
    require(expressions.contains(e1))
    require(expressions.contains(e2))

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sl,op,e1,e2)
      case _ =>  addExpression ( new PBinaryExpressionC(sl, op,e1, e2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePEqualityExpression(sl: SourceLocation,t1: PTerm,t2: PTerm) : PEqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new PEqualityExpressionC(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected val predicates = new HashMap[String, Predicate]

}