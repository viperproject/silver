package silAST.expressions

import silAST.domains.DomainPredicate
import silAST.source.SourceLocation
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import terms.{DTermFactory, GTerm, DTerm}
import util.{GTermSequence, DTermSequence}
import silAST.symbols.logical.quantification.{Quantifier, BoundVariable}
import collection.mutable.HashMap
import silAST.programs.NodeFactory


trait DExpressionFactory extends NodeFactory with GExpressionFactory with DTermFactory {
  //////////////////////////////////////////////////////////////////////////
  def makeDUnaryExpression(sl: SourceLocation, op: UnaryConnective, e1: DExpression): DUnaryExpression = {
    require(expressions contains e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sl, op, e1)
      case _ => addExpression(new DUnaryExpressionC(sl, op, e1))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDBinaryExpression(sl: SourceLocation, op: BinaryConnective, e1: DExpression, e2: DExpression): DBinaryExpression = {
    require(expressions contains e1)
    require(expressions contains e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sl, op, e1, e2)
      case _ => addExpression(new DBinaryExpressionC(sl, op, e1, e2))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDDomainPredicateExpression(sl: SourceLocation, p: DomainPredicate, args: DTermSequence): DDomainPredicateExpression = {
    require(domainPredicates contains p)
    require(args.forall(terms contains _))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sl, p, a)
      case _ => addExpression(new DDomainPredicateExpressionC(sl, p, args))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDEqualityExpression(sl: SourceLocation, t1: DTerm, t2: DTerm): DEqualityExpression = {
    require(terms contains t1)
    require(terms contains t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sl, t1, t2)
      case _ => addExpression[DEqualityExpression](new DEqualityExpressionC(sl, t1, t2))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDQuantifierExpression(sl: SourceLocation, q: Quantifier, v: BoundVariable, e: DExpression): DQuantifierExpression = {
    require(boundVariables contains v )
    require(!(boundVariableMap contains v))

    require(expressions contains e)

    val result = addExpression(new DQuantifierExpression(sl, q, v, e))
    boundVariableMap += v -> result

    result
  }

  //////////////////////////////////////////////////////////////////////////
  protected[silAST] val boundVariableMap = new HashMap[BoundVariable, QuantifierExpression]

}