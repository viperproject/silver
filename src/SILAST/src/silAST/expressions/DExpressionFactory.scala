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
  protected[silAST] def migrate(e: DExpression) {
    if (expressions contains e)
      return

    e match {
      case ge: GExpression => super.migrate(ge)
      case ue: DUnaryExpression => {
        migrate(ue.operand1)
      }
      case be: DBinaryExpression => {
        migrate(be.operand1)
        migrate(be.operand2)
      }
      case dpe: DDomainPredicateExpression => {
        require(domainPredicates contains dpe.predicate)
        dpe.arguments.foreach(migrate(_))
      }
      case ee: DEqualityExpression => {
        migrate(ee.term1)
        migrate(ee.term2)
      }
      case qe: DQuantifierExpression => {
        require(boundVariables contains qe.variable)
        require(!(boundVariableMap contains qe.variable))
        migrate(qe.expression)
      }
    }
    addExpression(e)
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDUnaryExpression(op: UnaryConnective, e1: DExpression)(sourceLocation: SourceLocation): DUnaryExpression = {
    migrate(e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(op, e1)(sourceLocation)
      case _ => addExpression(new DUnaryExpressionC(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDBinaryExpression(op: BinaryConnective, e1: DExpression, e2: DExpression)(sourceLocation: SourceLocation): DBinaryExpression = {
    migrate(e1)
    migrate(e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(op, e1, e2)(sourceLocation)
      case _ => addExpression(new DBinaryExpressionC(op, e1, e2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDDomainPredicateExpression(p: DomainPredicate, args: DTermSequence)(sourceLocation: SourceLocation): DDomainPredicateExpression = {
    require(domainPredicates contains p, "Unknown domain predicate %s.".format(p))
    args.foreach(migrate(_))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(p, a)(sourceLocation)
      case _ => addExpression(new DDomainPredicateExpressionC(sourceLocation, p, args))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDEqualityExpression(t1: DTerm, t2: DTerm)(sourceLocation: SourceLocation): DEqualityExpression = {
    migrate(t1)
    migrate(t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(t1, t2)(sourceLocation)
      case _ => addExpression[DEqualityExpression](new DEqualityExpressionC(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDQuantifierExpression(q: Quantifier, v: LogicalVariable, e: DExpression)(sourceLocation: SourceLocation): DQuantifierExpression = {
    require(boundVariables contains v)
    require(!(boundVariableMap contains v))

    migrate(e)

    val result = addExpression(new DQuantifierExpression(q, v, e)(sourceLocation))
    boundVariableMap += v -> result

    result
  }

  //////////////////////////////////////////////////////////////////////////
  protected[silAST] val boundVariableMap = new HashMap[LogicalVariable, QuantifierExpression]

}