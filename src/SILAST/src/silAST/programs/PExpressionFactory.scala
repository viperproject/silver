package silAST.programs

import collection.mutable.HashMap
import silAST.symbols.{Predicate,Function}
import silAST.source.SourceLocation
import silAST.expressions._
import terms.{PTerm, GeneralTerm}
import silAST.domains.DomainPredicate
import util.{GTermSequence, PTermSequence}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}


trait PExpressionFactory extends NodeFactory with GExpressionFactory
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
      case (t1: GeneralTerm, t2: GeneralTerm) => makeGEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new PEqualityExpressionC(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected val predicates = new HashMap[String, Predicate]
  protected val functions  = new HashMap[String, Function]

}