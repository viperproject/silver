package silAST.expressions

import silAST.domains.DomainPredicate
import silAST.source.SourceLocation
import collection.{mutable, Set}
import collection.mutable.HashSet
import silAST.expressions.util.GTermSequence
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import terms.{GTermFactory, GTerm}
import silAST.programs.NodeFactory


private[silAST] trait GExpressionFactory extends NodeFactory with GTermFactory {
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(e: GExpression) {
    if (expressions contains e)
      return

    e match {
      case ue: GUnaryExpression => {
        migrate(ue.operand1)
      }
      case be: GBinaryExpression => {
        migrate(be.operand1)
        migrate(be.operand2)
      }
      case dpe: GDomainPredicateExpression => {
        require(domainPredicates contains dpe.predicate)
        dpe.arguments.foreach(migrate(_))
      }
      case ee: GEqualityExpression => {
        migrate(ee.term1)
        migrate(ee.term2)
      }
      case te: TrueExpression => {}
      case fe: FalseExpression => {}
    }
    addExpression(e)
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGUnaryExpression(op: UnaryConnective, e1: GExpression,sourceLocation: SourceLocation,comment : List[String] = Nil): GUnaryExpression = {
    require(expressions contains e1)
    addExpression(new GUnaryExpression(op, e1)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGDomainPredicateExpression(p: DomainPredicate, args: GTermSequence,sourceLocation: SourceLocation,comment : List[String] = Nil): GDomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate(_))
    addExpression(new GDomainPredicateExpression(p, args)(sourceLocation,comment))
  }

  //////////////////////////////////////////////////////////////////////////
  def makeGBinaryExpression(op: BinaryConnective, e1: GExpression, e2: GExpression,sourceLocation: SourceLocation,comment : List[String] = Nil): GBinaryExpression = {
    migrate(e1)
    migrate(e2)

    addExpression(new GBinaryExpression(op, e1, e2)(sourceLocation,comment))

  }

  //////////////////////////////////////////////////////////////////////////
  def makeGEqualityExpression(

                               t1: GTerm,
                               t2: GTerm,
                               sourceLocation: SourceLocation,
                               comment : List[String] = Nil
                       ): GEqualityExpression = {
    migrate(t1)
    migrate(t2)
    addExpression(new GEqualityExpression(t1, t2)(sourceLocation,comment))
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

  protected[expressions] val pExpressions = new mutable.HashSet[Expression]

  protected[silAST] def expressions: Set[Expression] = pExpressions

  protected[silAST] def domainPredicates: Set[DomainPredicate]

}