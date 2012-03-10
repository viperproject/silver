package silAST.expressions

import silAST.domains.DomainPredicate
import silAST.source.SourceLocation
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import terms.{DTermFactory, GTerm, DTerm}
import util.{GTermSequence, DTermSequence}
import silAST.symbols.logical.quantification.{Quantifier, LogicalVariable}
import collection.mutable.HashMap
import silAST.programs.NodeFactory


trait DExpressionFactory extends NodeFactory with GExpressionFactory with DTermFactory {
  //////////////////////////////////////////////////////////////////////////
  def makeDUnaryExpression(sourceLocation : SourceLocation, op: UnaryConnective, e1: DExpression): DUnaryExpression = {
    require(expressions contains e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sourceLocation, op, e1)
      case _ => addExpression(new DUnaryExpressionC(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDBinaryExpression(sourceLocation : SourceLocation, op: BinaryConnective, e1: DExpression, e2: DExpression): DBinaryExpression = {
    require(expressions contains e1)
    require(expressions contains e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sourceLocation, op, e1, e2)
      case _ => addExpression(new DBinaryExpressionC(op, e1, e2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDDomainPredicateExpression(sourceLocation : SourceLocation, p: DomainPredicate, args: DTermSequence): DDomainPredicateExpression = {
    require(domainPredicates contains p,"Unknown domain predicate %s.".format(p))
    require(args.forall(terms contains _),"At least one of the terms in [%s] is not known.".format(args))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sourceLocation, p, a)
      case _ => addExpression(new DDomainPredicateExpressionC(sourceLocation, p, args))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDEqualityExpression(sourceLocation : SourceLocation, t1: DTerm, t2: DTerm): DEqualityExpression = {
    require(terms contains t1)
    require(terms contains t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sourceLocation, t1, t2)
      case _ => addExpression[DEqualityExpression](new DEqualityExpressionC(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDQuantifierExpression(sourceLocation : SourceLocation, q: Quantifier, v: LogicalVariable, e: DExpression): DQuantifierExpression = {
    require(boundVariables contains v)
    require(!(boundVariableMap contains v))

    require(expressions contains e)

    val result = addExpression(new DQuantifierExpression(q, v, e)(sourceLocation))
    boundVariableMap += v -> result

    result
  }

  //////////////////////////////////////////////////////////////////////////
  protected[silAST] val boundVariableMap = new HashMap[LogicalVariable, QuantifierExpression]

}