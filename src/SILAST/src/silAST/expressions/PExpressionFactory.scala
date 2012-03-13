package silAST.expressions

import silAST.source.SourceLocation
import silAST.domains.DomainPredicate
import terms.{PTermFactory, PTerm, GTerm}
import util.{GTermSequence, PTermSequence}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.programs.NodeFactory
import silAST.programs.symbols.{ProgramVariable, Predicate}
import collection.{immutable, Set}


trait PExpressionFactory extends NodeFactory with GExpressionFactory with PTermFactory {
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(e:PExpression)
  {
    if (expressions contains e)
      return

    e match {
      case ge : GExpression => super.migrate(ge)
      case ue : PUnaryExpression => {
        migrate(ue.operand1)
      }
      case be : PBinaryExpression => {
        migrate(be.operand1)
        migrate(be.operand2)
      }
      case dpe : PDomainPredicateExpression => {
        require(domainPredicates contains dpe.predicate)
        dpe.arguments.foreach(migrate(_))
      }
      case ee : PEqualityExpression =>
      {
        migrate(ee.term1)
        migrate(ee.term2)
      }
      case ppe : PPredicateExpression => {
        require(predicates contains ppe.predicate)
      }
      case pue : PUnfoldingExpression => {
        migrate(pue.expression)
        migrate(pue.predicate)
      }
    }
    addExpression(e)
  }

  //////////////////////////////////////////////////////////////////////////
  def makePDomainPredicateExpression(sourceLocation : SourceLocation, p: DomainPredicate, args: PTermSequence): PDomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate(_))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(sourceLocation, p, a)
      case _ => addExpression(new PDomainPredicateExpressionC(p, args)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePPredicateExpression(sourceLocation : SourceLocation, r: PTerm, p: Predicate): PPredicateExpression = {
    require(predicates contains p)
    migrate(r)

    addExpression(new PPredicateExpression(r, p)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnaryExpression(sourceLocation : SourceLocation, op: UnaryConnective, e1: PExpression): PUnaryExpression = {
    migrate(e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(sourceLocation, op, e1)
      case _ => addExpression(new PUnaryExpressionC(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePBinaryExpression(sourceLocation : SourceLocation, op: BinaryConnective, e1: PExpression, e2: PExpression): PBinaryExpression = {
    migrate(e1)
    migrate(e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(sourceLocation, op, e1, e2)
      case _ => addExpression(new PBinaryExpressionC(op, e1, e2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePEqualityExpression(sourceLocation : SourceLocation, t1: PTerm, t2: PTerm): PEqualityExpression = {
    migrate(t1)
    migrate(t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(sourceLocation, t1, t2)
      case _ => addExpression(new PEqualityExpressionC(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingExpression(sourceLocation : SourceLocation, p: PPredicateExpression, e: PExpression): UnfoldingExpression = {
    migrate(p)
    migrate(e)

    addExpression(new PUnfoldingExpression(p, e)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def predicates: Set[Predicate]
}