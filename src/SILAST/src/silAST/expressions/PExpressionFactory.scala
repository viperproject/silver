package silAST.expressions

import silAST.source.SourceLocation
import silAST.domains.DomainPredicate
import terms.{PTermFactory, PTerm, GTerm}
import util.{GTermSequence, PTermSequence}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.programs.NodeFactory
import collection.Set
import silAST.programs.symbols.{ProgramVariableSequence, ProgramVariable, Predicate}
import collection.mutable.HashSet


trait PExpressionFactory extends NodeFactory with GExpressionFactory with PTermFactory {
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(e: PExpression) {
    if (expressions contains e)
      return

    e match {
      case ge: GExpression => super.migrate(ge)
      case ue: PUnaryExpression => {
        migrate(ue.operand1)
      }
      case be: PBinaryExpression => {
        migrate(be.operand1)
        migrate(be.operand2)
      }
      case dpe: PDomainPredicateExpression => {
        require(domainPredicates contains dpe.predicate)
        dpe.arguments.foreach(migrate(_))
      }
      case ee: PEqualityExpression => {
        migrate(ee.term1)
        migrate(ee.term2)
      }
      case ppe: PPredicateExpression => {
        require(predicates contains ppe.predicate)
      }
      case pue: PUnfoldingExpression => {
        migrate(pue.expression)
        migrate(pue.predicate)
      }
    }
    addExpression(e)
  }

  //////////////////////////////////////////////////////////////////
  def makeProgramVariableSequence(vs: Seq[ProgramVariable])(sourceLocation: SourceLocation): ProgramVariableSequence = {
    require(vs.forall(programVariables contains _))
    val result = new ProgramVariableSequence(vs)(sourceLocation)
    programVariableSequences += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def makePDomainPredicateExpression(p: DomainPredicate, args: PTermSequence)(sourceLocation: SourceLocation): PDomainPredicateExpression = {
    require(domainPredicates contains p)
    args.foreach(migrate(_))

    (args) match {
      case (a: GTermSequence) => makeGDomainPredicateExpression(p, a)(sourceLocation)
      case _ => addExpression(new PDomainPredicateExpressionC(p, args)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePPredicateExpression(r: PTerm, p: Predicate)(sourceLocation: SourceLocation): PPredicateExpression = {
    require(predicates contains p)
    migrate(r)

    addExpression(new PPredicateExpression(r, p)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnaryExpression(op: UnaryConnective, e1: PExpression)(sourceLocation: SourceLocation): PUnaryExpression = {
    migrate(e1)

    (e1) match {
      case (e1: GExpression) => makeGUnaryExpression(op, e1)(sourceLocation)
      case _ => addExpression(new PUnaryExpressionC(op, e1)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePBinaryExpression(op: BinaryConnective, e1: PExpression, e2: PExpression)(sourceLocation: SourceLocation): PBinaryExpression = {
    migrate(e1)
    migrate(e2)

    (e1, e2) match {
      case (e1: GExpression, e2: GExpression) => makeGBinaryExpression(op, e1, e2)(sourceLocation)
      case _ => addExpression(new PBinaryExpressionC(op, e1, e2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePEqualityExpression(t1: PTerm, t2: PTerm)(sourceLocation: SourceLocation): PEqualityExpression = {
    migrate(t1)
    migrate(t2)

    (t1, t2) match {
      case (t1: GTerm, t2: GTerm) => makeGEqualityExpression(t1, t2)(sourceLocation)
      case _ => addExpression(new PEqualityExpressionC(t1, t2)(sourceLocation))
    }
  }

  //////////////////////////////////////////////////////////////////////////
  def makePUnfoldingExpression(p: PPredicateExpression, e: PExpression)(sourceLocation: SourceLocation): UnfoldingExpression = {
    migrate(p)
    migrate(e)

    addExpression(new PUnfoldingExpression(p, e)(sourceLocation))
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def predicates: Set[Predicate]

  protected[silAST] val programVariableSequences = new HashSet[ProgramVariableSequence]
}