package silAST.programs

import silAST.domains.{DomainFunction, DomainPredicate}
import silAST.source.SourceLocation
import collection.mutable.{HashSet, HashMap}
import silAST.expressions.util.{GTermSequence, ExpressionSequence, TermSequence}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.expressions._
import terms.{GTerm, Term}


private[silAST] trait GExpressionFactory extends NodeFactory
{
  //////////////////////////////////////////////////////////////////////////
  def makeGUnaryExpression(sl: SourceLocation,op:UnaryConnective,e1: GExpression): GUnaryExpression = {
    require(expressions.contains(e1))

    addExpression ( new GUnaryExpression(sl,op, e1) )
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGDomainPredicateExpression(sl: SourceLocation,p : DomainPredicate, args : GTermSequence): GDomainPredicateExpression =
  {
    require(domainPredicates(p.name) == p)
    require(termSequences.contains(args))
    addExpression ( new GDomainPredicateExpression(sl,p,args) )
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGBinaryExpression(sl: SourceLocation,op:BinaryConnective,e1: GExpression, e2:GExpression): GBinaryExpression = {
    require(expressions.contains(e1))
    require(expressions.contains(e2))

    addExpression ( new GBinaryExpression(sl,op, e1, e2) )

  }

  //////////////////////////////////////////////////////////////////////////
  def makeGEqualityExpression(
                              sl: SourceLocation,
                              t1: GTerm,
                              t2: GTerm
                              ): GEqualityExpression =
  {
    require(terms.contains(t1))
    require(terms.contains(t2))
    addExpression ( new GEqualityExpression(sl, t1, t2) )
  }



  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected def addExpression[E <: Expression](e: E)  : E = {
    expressions + e
    nodeMap += e.sourceLocation -> e    //Overrides sub expressions - always largest in the map
    e
  }
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected val terms = new HashSet[Term]
  protected val expressions = new HashSet[Expression]

  protected val termSequences = new HashSet[TermSequence]
  protected val expressionSequences = new HashSet[ExpressionSequence]
  protected val domainPredicates = new HashMap[String, DomainPredicate]
  protected val domainFunctions  = new HashMap[String, DomainFunction]

}