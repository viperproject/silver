package silAST.expressions

import scala.collection.Seq

import silAST.domains.DomainPredicate
import silAST.expressions.terms.permission.PermissionTerm
import silAST.symbols.logical.quantification.{Quantifier, BoundVariable}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.ASTNode
import terms.{GTerm, Term, PTerm, DTerm}
import util.{GTermSequence, TermSequence, PTermSequence, DTermSequence}
import silAST.programs.symbols.Predicate
import silAST.source.{noLocation, SourceLocation}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression protected[silAST](
                                                    sl: SourceLocation
                                                    ) extends ASTNode(sl) {
  val subExpressions: Seq[Expression]
}


///////////////////////////////////////////////////////////////////////////

sealed trait AtomicExpression extends Expression {
  override val subExpressions: Seq[Expression] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class PermissionExpression private[silAST](
                                                       sl: SourceLocation,
                                                       reference: Term,
                                                       permission: PermissionTerm
                                                       )
  extends Expression(sl)
  with AtomicExpression {
  override val toString = "acc(" + reference.toString + "," + permission.toString + ")"

  override val subNodes = List(reference, permission)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingExpression private[silAST](
                                                      sl: SourceLocation,
                                                      predicate: PredicateExpression,
                                                      expression: Expression
                                                      ) extends Expression(sl) {
  override val toString = "unfolding " + predicate.toString + " in " + expression.toString

  override val subNodes: Seq[ASTNode] = List(predicate, expression)

  override val subExpressions: Seq[Expression] = List(expression)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class EqualityExpression private[silAST](
                                                      sl: SourceLocation,
                                                      term1: Term,
                                                      term2: Term
                                                      )
  extends Expression(sl) {

  override val toString = term1.toString + "=" + term2.toString

  override val subNodes = List(term1, term2)
  override val subExpressions: Seq[Expression] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnaryExpression private[silAST](
                                                   sl: SourceLocation,
                                                   operator: UnaryConnective,
                                                   operand1: Expression
                                                   ) extends Expression(sl) {
  override val toString = operator.toString + operand1.toString

  override val subNodes = List(operator, operand1)

  override val subExpressions: Seq[Expression] = List(operand1)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class BinaryExpression private[silAST](
                                                    sl: SourceLocation,
                                                    operator: BinaryConnective,
                                                    operand1: Expression,
                                                    operand2: Expression
                                                    ) extends Expression(sl) {
  override val toString = operand1.toString + " " + operator.toString + " " + operand2.toString

  override val subNodes = List(operand1, operator, operand2)

  override val subExpressions: Seq[Expression] = List(operand1, operand2)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainPredicateExpression private[silAST](
                                                             sl: SourceLocation,
                                                             predicate: DomainPredicate,
                                                             arguments: TermSequence
                                                             ) extends Expression(sl)
with AtomicExpression {
  override val toString: String = predicate.name + arguments.toString

  override val subNodes: Seq[ASTNode] = List(predicate, arguments)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PredicateExpression private[silAST](
                                                       sl: SourceLocation,
                                                       receiver: Term,
                                                       predicate: Predicate
                                                       ) extends Expression(sl)
with AtomicExpression {

  override val toString = receiver + "." + predicate.name

  override val subNodes: Seq[ASTNode] = List(receiver, predicate)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class QuantifierExpression private[silAST](
                                                        sl: SourceLocation,
                                                        quantifier: Quantifier,
                                                        variable: BoundVariable,
                                                        expression: Expression
                                                        )
  extends Expression(sl) {
  override val toString = quantifier.toString + " " + variable.name + " : " + variable.dataType.toString + " :: (" + expression.toString + ")"

  override val subNodes: Seq[ASTNode] = List(quantifier, variable, expression)

  override val subExpressions: Seq[Expression] = List(expression)
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PExpression
  extends Expression {
  override val subExpressions: Seq[PExpression] = pSubExpressions

  protected[expressions] def pSubExpressions: Seq[PExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PEqualityExpression
  extends EqualityExpression
  with PExpression {
  override val term1: PTerm = pTerm1
  override val term2: PTerm = pTerm2

  protected[expressions] def pTerm1: PTerm

  protected[expressions] def pTerm2: PTerm
}

object PEqualityExpression {
  def unapply(pee: PEqualityExpression): Option[(SourceLocation, PTerm, PTerm)] = Some(pee.sl, pee.term1, pee.term2)
}

private[silAST] final class PEqualityExpressionC(
                                                  sl: SourceLocation,
                                                  term1: PTerm,
                                                  term2: PTerm
                                                  )
  extends EqualityExpression(sl, term1, term2)
  with PEqualityExpression {
  override val pSubExpressions = subExpressions
  override val pTerm1: PTerm = term1
  override val pTerm2: PTerm = term2
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnfoldingExpression private[silAST](
                                                       sl: SourceLocation,
                                                       predicate: PPredicateExpression,
                                                       expression: PExpression
                                                       ) extends UnfoldingExpression(sl,predicate,expression) with PExpression
{
  override val toString = "unfolding " + predicate.toString + " in " + expression.toString

  override val subNodes: Seq[ASTNode] = List(predicate, expression)

  override val pSubExpressions: Seq[PExpression] = List(predicate,expression)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PUnaryExpression extends UnaryExpression with PExpression {
  override val operand1: PExpression = pOperand1

  protected[expressions] def pOperand1: PExpression
}

object PUnaryExpression {
  def unapply(pube: PUnaryExpression): Option[(SourceLocation, UnaryConnective, PExpression)] =
    Some(pube.sl, pube.operator, pube.operand1)
}

private[silAST] final class PUnaryExpressionC private[silAST](
                                                               sl: SourceLocation,
                                                               override val operator: UnaryConnective,
                                                               override val operand1: PExpression
                                                               )
  extends UnaryExpression(sl, operator, operand1)
  with PUnaryExpression {
  override val pSubExpressions: Seq[PExpression] = List(operand1)
  override val pOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PBinaryExpression extends BinaryExpression with PExpression {
  override val operand1: PExpression = pOperand1
  override val operand2: PExpression = pOperand2

  protected[expressions] def pOperand1: PExpression

  protected[expressions] def pOperand2: PExpression
}

object PBinaryExpression {
  def unapply(pbbe: PBinaryExpression): Option[(SourceLocation, BinaryConnective, PExpression, PExpression)] =
    Some(pbbe.sl, pbbe.operator, pbbe.operand1, pbbe.operand2)
}

private[silAST] final class PBinaryExpressionC private[silAST](
                                                                sl: SourceLocation,
                                                                override val operator: BinaryConnective,
                                                                override val operand1: PExpression,
                                                                override val operand2: PExpression
                                                                )
  extends BinaryExpression(sl, operator, operand1, operand2)
  with PBinaryExpression {
  override val pSubExpressions: Seq[PExpression] = List(operand1, operand2)
  override val pOperand1 = operand1
  override val pOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainPredicateExpression extends DomainPredicateExpression with PExpression {
  override val arguments: PTermSequence = pArguments
  protected[expressions] val pArguments: PTermSequence
}

private[silAST] final class PDomainPredicateExpressionC(
                                                         sl: SourceLocation,
                                                         override val predicate: DomainPredicate,
                                                         override val arguments: PTermSequence
                                                         )
  extends DomainPredicateExpression(sl, predicate, arguments)
  with PDomainPredicateExpression
  with AtomicExpression {
  override val pArguments = arguments
  override val pSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PPredicateExpression private[silAST](
                                                  sl: SourceLocation,
                                                  override val receiver: PTerm,
                                                  override val predicate: Predicate
                                                  )
  extends PredicateExpression(sl, receiver, predicate)
  with PExpression {
  override val pSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DExpression
  extends Expression {
  override val subExpressions: Seq[DExpression] = dSubExpressions
  protected[expressions] val dSubExpressions: Seq[DExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DEqualityExpression
  extends EqualityExpression
  with DExpression {
  override val term1: DTerm = dTerm1
  override val term2: DTerm = dTerm2

  protected[expressions] val dTerm1: DTerm
  protected[expressions] val dTerm2: DTerm

}

private[silAST] final class DEqualityExpressionC(
                                                  sl: SourceLocation,
                                                  term1: DTerm,
                                                  term2: DTerm
                                                  )
  extends EqualityExpression(sl, term1, term2)
  with DEqualityExpression {
  override val dTerm1 = term1
  override val dTerm2 = term2

  override val dSubExpressions = subExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DUnaryExpression extends UnaryExpression with DExpression {
  override val operand1: DExpression = dOperand1
  protected[expressions] val dOperand1: DExpression
}

object DUnaryExpression {
  def unapply(dube: DUnaryExpression): Option[(SourceLocation, UnaryConnective, DExpression)] =
    Some(dube.sl, dube.operator, dube.operand1)
}

private[silAST] final class DUnaryExpressionC private[silAST](
                                                               sl: SourceLocation,
                                                               override val operator: UnaryConnective,
                                                               override val operand1: DExpression
                                                               )
  extends UnaryExpression(sl, operator, operand1)
  with DUnaryExpression {
  override val dSubExpressions: Seq[DExpression] = List(operand1)
  override val dOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DBinaryExpression extends BinaryExpression with DExpression {
  override val operand1: DExpression = dOperand1
  override val operand2: DExpression = dOperand2

  protected[expressions] val dOperand1: DExpression
  protected[expressions] val dOperand2: DExpression
}

object DBinaryExpression {
  def unapply(dbbe: DBinaryExpression): Option[(SourceLocation, BinaryConnective, DExpression, DExpression)] =
    Some(dbbe.sl, dbbe.operator, dbbe.operand1, dbbe.operand2)
}

private[silAST] final class DBinaryExpressionC private[silAST](
                                                                sl: SourceLocation,
                                                                override val operator: BinaryConnective,
                                                                override val operand1: DExpression,
                                                                override val operand2: DExpression
                                                                )
  extends BinaryExpression(sl, operator, operand1, operand2)
  with DBinaryExpression {
  override val dSubExpressions: Seq[DExpression] = List(operand1, operand2)
  override val dOperand1 = operand1
  override val dOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainPredicateExpression extends DomainPredicateExpression with DExpression {
  override val arguments: DTermSequence = dArguments

  protected[expressions] def dArguments: DTermSequence
}

private[silAST] final class DDomainPredicateExpressionC(
                                                         sl: SourceLocation,
                                                         override val predicate: DomainPredicate,
                                                         override val arguments: DTermSequence
                                                         )
  extends DomainPredicateExpression(sl, predicate, arguments)
  with DDomainPredicateExpression
  with AtomicExpression {
  override val dArguments = arguments
  override val dSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DQuantifierExpression private[silAST](
                                                   sl: SourceLocation,
                                                   override val quantifier: Quantifier,
                                                   override val variable: BoundVariable,
                                                   override val expression: DExpression
                                                   )
  extends QuantifierExpression(sl, quantifier, variable, expression)
  with DExpression {
  override val subExpressions: Seq[DExpression] = List(expression)
  override val dSubExpressions = subExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//General/ground
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait GExpression
  extends Expression with DExpression with PExpression {
  override val subExpressions: Seq[GExpression] = gSubExpressions
  protected[expressions] final override val pSubExpressions = subExpressions
  protected[expressions] final override val dSubExpressions = subExpressions

  protected[expressions] def gSubExpressions: Seq[GExpression]
}

///////////////////////////////////////////////////////////////////////////
final class GEqualityExpression private[silAST](
                                                 sl: SourceLocation,
                                                 override val term1: GTerm,
                                                 override val term2: GTerm
                                                 )
  extends EqualityExpression(sl, term1, term2)
  with PEqualityExpression with DEqualityExpression with GExpression {
  override val subExpressions: Seq[GExpression] = Nil
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pTerm1 = term1
  protected[expressions] override val pTerm2 = term2
  protected[expressions] override val dTerm1 = term1
  protected[expressions] override val dTerm2 = term2
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GUnaryExpression private[silAST](
                                              sl: SourceLocation,
                                              operator: UnaryConnective,
                                              override val operand1: GExpression
                                              ) extends UnaryExpression(sl, operator, operand1)
with PUnaryExpression
with DUnaryExpression
with GExpression {
  override val subNodes = List(operator, operand1)

  override val subExpressions = List(operand1)
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GBinaryExpression private[silAST](
                                               sl: SourceLocation,
                                               operator: BinaryConnective,
                                               override val operand1: GExpression,
                                               override val operand2: GExpression
                                               ) extends BinaryExpression(sl, operator, operand1, operand2)
with PBinaryExpression
with DBinaryExpression
with GExpression {

  override val subNodes = List(operand1, operator, operand2)

  override val subExpressions = List(operand1, operand2)

  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1
  protected[expressions] override val pOperand2 = operand2
  protected[expressions] override val dOperand2 = operand2
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GDomainPredicateExpression private[silAST](
                                                        sl: SourceLocation,
                                                        predicate: DomainPredicate,
                                                        override val arguments: GTermSequence
                                                        ) extends DomainPredicateExpression(sl, predicate, arguments)
with PDomainPredicateExpression
with DDomainPredicateExpression
with GExpression {
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val dArguments = arguments
  protected[expressions] override val pArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class TrueExpression private[silAST]() extends Expression(noLocation)
with GExpression with AtomicExpression {
  override val subNodes = List.empty

  override val subExpressions = List.empty
  override val gSubExpressions = List.empty
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class FalseExpression private[silAST]() extends Expression(noLocation)
with GExpression with AtomicExpression {
  override val subNodes = List.empty

  override val subExpressions = List.empty
  override val gSubExpressions = List.empty
}

