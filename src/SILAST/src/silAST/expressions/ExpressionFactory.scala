package silAST.expressions

import silAST.source.SourceLocation
import collection.mutable.HashSet
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.domains.DomainPredicate
import terms._
import permission.{PermissionFactory, PermissionTerm}
import util._
import silAST.symbols.logical.quantification.{BoundVariable, Quantifier}
import silAST.programs.NodeFactory
import silAST.programs.symbols.Predicate


trait ExpressionFactory extends NodeFactory with DExpressionFactory with PExpressionFactory with TermFactory with PermissionFactory{
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeUnaryExpression(sl: SourceLocation,op:UnaryConnective,e1: Expression): UnaryExpression = {
    require(expressions.contains(e1))

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sl,op,e1)
      case (e1: PExpression) => makePUnaryExpression(sl,op,e1)
      case (e1: DExpression) => makeDUnaryExpression(sl,op,e1)
      case _ =>  addExpression ( new UnaryExpression(sl, op, e1) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeBinaryExpression(sl: SourceLocation,op:BinaryConnective,e1: Expression, e2:Expression): BinaryExpression = {
    require(expressions.contains(e1))
    require(expressions.contains(e2))

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sl,op,e1,e2)
      case (e1: PExpression, e2: PExpression) => makePBinaryExpression(sl,op,e1,e2)
      case (e1: DExpression, e2: DExpression) => makeDBinaryExpression(sl,op,e1,e2)
      case _ =>  addExpression ( new BinaryExpression(sl, op, e1, e2) )
    }
  }


  //////////////////////////////////////////////////////////////////////////
  def makeDomainPredicateExpression(sl: SourceLocation,p : DomainPredicate, args : TermSequence): DomainPredicateExpression =
  {
    require(domainPredicates(p.name) == p)
    require(termSequences.contains(args))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sl,p,a)
      case (a: PTermSequence) => makePDomainPredicateExpression(sl,p,a)
      case (a: DTermSequence) => makeDDomainPredicateExpression(sl,p,a)
      case _ =>  addExpression ( new DomainPredicateExpression(sl,p,args))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePredicateExpression(sl: SourceLocation, r : Term,p : Predicate): PredicateExpression =
  {
    require(predicates contains p)
    require(terms.contains(r))

    (r) match {
      case (r: PTerm) => makePPredicateExpression(sl,r,p)
      case _ =>  addExpression ( new PredicateExpression(sl,r,p))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeEqualityExpression(sl: SourceLocation,t1: Term,t2: Term): EqualityExpression = {
    require(terms.contains(t1))
    require(terms.contains(t2))

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sl,t1,t2)
      case (t1: PTerm, t2: PTerm) => makePEqualityExpression(sl,t1,t2)
      case (t1: DTerm, t2: DTerm)   => makeDEqualityExpression(sl,t1,t2)
      case _ =>  addExpression ( new EqualityExpression(sl, t1, t2) )
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeQuantifierExpression(sl: SourceLocation,q : Quantifier, v : BoundVariable, e : Expression) : QuantifierExpression = {
    require(boundVariables.contains(v))
    require(!boundVariableMap.contains(v))

    require(expressions.contains(e))

    e match{
      case e : DExpression => makeDQuantifierExpression(sl,q,v,e)
      case _ =>{
        val result = addExpression(new QuantifierExpression(sl,q,v,e))
        boundVariableMap += v -> result

        result
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePermissionExpression(sl: SourceLocation,r: Term,p: PermissionTerm) : PermissionExpression =
  {
    require(terms.contains(r))
    require(permissionTerms.contains(p))

    addExpression(new PermissionExpression(sl,r,p))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeUnfoldingExpression(sl: SourceLocation, p : Term, e : Expression) : UnfoldingExpression =
  {
    require(terms.contains(p))
    require(expressions.contains(e))

    addExpression(new UnfoldingExpression(sl,p,e))
  }

  //////////////////////////////////////////////////////////////////////////
//  protected[silAST] val permissionTerms = new HashSet[PermissionTerm]
}