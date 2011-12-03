package silAST.expressions

import scala.collection.Seq

import silAST.domains.DomainPredicate
import silAST.expressions.terms.permission.PermissionTerm
import silAST.expressions.util.{TermSequence, PTermSequence, DTermSequence}
import silAST.symbols.logical.quantification.{Quantifier, BoundVariable}
import silAST.symbols.logical.{UnaryBooleanOperator, BinaryBooleanOperator}
import silAST.symbols.Predicate
import silAST.ASTNode
import silAST.source.SourceLocation
import terms.{GeneralTerm, Term, ProgramTerm, DomainTerm}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression protected[silAST](
                                                    sl: SourceLocation
                                                    ) extends ASTNode(sl) {
  val subExpressions: Seq[Expression]
}


///////////////////////////////////////////////////////////////////////////

sealed trait AtomicExpression extends Expression {
  override val subExpressions : Seq[Expression] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class AccessPermissionExpression private[silAST](
                                                             sl: SourceLocation,
                                                             reference: Term,
                                                             permission: PermissionTerm
                                                             )
  extends Expression(sl)
  with AtomicExpression
{
  override val toString = "acc(" + reference.toString + "," + permission.toString + ")"

  override val subNodes = List(reference,permission)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class UnfoldingExpression private[silAST](
                                                sl: SourceLocation,
                                                predicate: Term,
                                                expression: Expression
                                                ) extends Expression(sl) {
  override val toString = "unfolding " + predicate.toString + " in " + expression.toString

  override val subNodes : Seq[ASTNode] = List(predicate, expression)

  override val subExpressions : Seq[Expression] = List(expression)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class EqualityExpression private[silAST](
                                               sl: SourceLocation,
                                               term1: Term,
                                               term2: Term
                                               )
  extends Expression(sl)
{

  override val toString = term1.toString + "=" + term2.toString

  override val subNodes = List(term1,term2)
  override val subExpressions : Seq[Expression] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnaryBooleanExpression private[silAST](
                                                   sl: SourceLocation,
                                                   operator: UnaryBooleanOperator,
                                                   operand1: Expression
                                                   ) extends Expression(sl) {
  override val toString = operator.toString + operand1.toString

  override val subNodes = List(operator,operand1)

  override val subExpressions : Seq[Expression] = List(operand1)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class BinaryBooleanExpression private[silAST](
                                                    sl: SourceLocation,
                                                    operator: BinaryBooleanOperator,
                                                    operand1: Expression,
                                                    operand2: Expression
                                                    ) extends Expression(sl) {
  override val toString = operand1.toString + " " + operator.toString + " " + operand2.toString

  override val subNodes = List(operand1,operator,operand2)

  override val subExpressions : Seq[Expression] = List(operand1,operand2)
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

  override val subNodes : Seq[ASTNode]  = List(predicate,arguments)
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

  override val subNodes : Seq[ASTNode]  = List(receiver, predicate)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class QuantifierExpression private[silAST](
                                                 sl: SourceLocation,
                                                 quantifier: Quantifier,
                                                 variable: BoundVariable,
                                                 expression: Expression
                                                 )
  extends Expression(sl)
{
  override val toString = quantifier.toString + " " + variable.name + " : " + variable.dataType.toString + " :: (" + expression.toString + ")"

  override val subNodes : Seq[ASTNode] = List(quantifier,variable,expression)

  override val subExpressions : Seq[Expression] = List(expression)
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
sealed trait ProgramExpression
  extends Expression
{
  override val subExpressions : Seq[ProgramExpression] = pSubExpressions

  protected[expressions] val pSubExpressions :Seq[ProgramExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PEqualityExpression
  extends EqualityExpression
  with ProgramExpression
{
  override val term1 : ProgramTerm = pTerm1
  override val term2 : ProgramTerm = pTerm2

  protected[expressions] val pTerm1 : ProgramTerm
  protected[expressions] val pTerm2 : ProgramTerm
}

object PEqualityExpression{
  def unapply(pee : PEqualityExpression) : Option[(SourceLocation,ProgramTerm,ProgramTerm)] = Some(pee.sl, pee.term1,pee.term2)
}

private[silAST] final class PEqualityExpressionC(
                                                 sl: SourceLocation,
                                                 term1: ProgramTerm,
                                                 term2: ProgramTerm
                                                 )
  extends EqualityExpression(sl, term1, term2)
  with PEqualityExpression
{
  override val pSubExpressions = subExpressions
  override val pTerm1 : ProgramTerm = term1
  override val pTerm2 : ProgramTerm = term2
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PUnaryBooleanExpression extends UnaryBooleanExpression with ProgramExpression
{
  override val operand1 : ProgramExpression = pOperand1
  protected[expressions] val pOperand1 : ProgramExpression
}

object PUnaryBooleanExpression{
  def unapply(pube : PUnaryBooleanExpression) : Option[(SourceLocation,UnaryBooleanOperator,ProgramExpression)] =
    Some(pube.sl, pube.operator,pube.operand1)
}

private[silAST] final class PUnaryBooleanExpressionC private[silAST](
                                                     sl: SourceLocation,
                                                     override val operator: UnaryBooleanOperator,
                                                     override val operand1: ProgramExpression
                                                     )
  extends UnaryBooleanExpression(sl, operator, operand1)
  with PUnaryBooleanExpression
{
  override val pSubExpressions: Seq[ProgramExpression] = List(operand1)
  override val pOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PBinaryBooleanExpression extends BinaryBooleanExpression with ProgramExpression{
  override val operand1 : ProgramExpression = pOperand1
  override val operand2 : ProgramExpression = pOperand2

  protected[expressions] val pOperand1 : ProgramExpression
  protected[expressions] val pOperand2 : ProgramExpression
}

object PBinaryBooleanExpression{
  def unapply(pbbe : PBinaryBooleanExpression) : Option[(SourceLocation,BinaryBooleanOperator,ProgramExpression,ProgramExpression)] =
    Some(pbbe.sl, pbbe.operator,pbbe.operand1,pbbe.operand2)
}

private[silAST] final class PBinaryBooleanExpressionC private[silAST](
                                                     sl: SourceLocation,
                                                     override val operator: BinaryBooleanOperator,
                                                     override val operand1: ProgramExpression,
                                                     override val operand2: ProgramExpression
                                                     )
  extends BinaryBooleanExpression(sl, operator, operand1,operand2)
  with PBinaryBooleanExpression
{
  override val pSubExpressions: Seq[ProgramExpression] = List(operand1,operand2)
  override val pOperand1 = operand1
  override val pOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainPredicateExpression extends DomainPredicateExpression with ProgramExpression
{
  override val arguments: PTermSequence = pArguments
  protected[expressions] val pArguments : PTermSequence
}

private[silAST] final class PDomainPredicateExpressionC (
                                                        sl: SourceLocation,
                                                        override val predicate: DomainPredicate,
                                                        override val arguments: PTermSequence
                                                        )
  extends DomainPredicateExpression(sl, predicate, arguments)
  with PDomainPredicateExpression
  with AtomicExpression
{
  override val pArguments = arguments
  override val pSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PPredicateExpression private[silAST](
    sl: SourceLocation,
    override val receiver: ProgramTerm,
    override val predicate: Predicate
  )
  extends PredicateExpression(sl, receiver, predicate)
  with ProgramExpression
{
  override val pSubExpressions = Nil
}
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DomainExpression
  extends Expression
{
  override val subExpressions : Seq[DomainExpression] = dSubExpressions
  protected[expressions] val dSubExpressions : Seq[DomainExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DEqualityExpression
  extends EqualityExpression
  with DomainExpression
{
  override val term1 : DomainTerm = dTerm1
  override val term2 : DomainTerm = dTerm2

  protected[expressions] val dTerm1 : DomainTerm
  protected[expressions] val dTerm2 : DomainTerm

}

private[silAST] final class DEqualityExpressionC(
                                                 sl: SourceLocation,
                                                 term1: DomainTerm,
                                                 term2: DomainTerm
                                                 )
  extends EqualityExpression(sl, term1, term2)
  with DEqualityExpression
{
  override val dTerm1 = term1
  override val dTerm2 = term2

  override val dSubExpressions = subExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DUnaryBooleanExpression extends UnaryBooleanExpression with DomainExpression{
  override val operand1 : DomainExpression = dOperand1
  protected[expressions] val dOperand1 : DomainExpression
}

object DUnaryBooleanExpression{
  def unapply(dube : DUnaryBooleanExpression) : Option[(SourceLocation,UnaryBooleanOperator,DomainExpression)] =
    Some(dube.sl, dube.operator,dube.operand1)
}

private[silAST] final class DUnaryBooleanExpressionC private[silAST](
                                                     sl: SourceLocation,
                                                     override val operator: UnaryBooleanOperator,
                                                     override val operand1: DomainExpression
                                                     )
  extends UnaryBooleanExpression(sl, operator, operand1)
  with DUnaryBooleanExpression
{
  override val dSubExpressions: Seq[DomainExpression] = List(operand1)
  override val dOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DBinaryBooleanExpression extends BinaryBooleanExpression with DomainExpression{
  override val operand1 : DomainExpression = dOperand1
  override val operand2 : DomainExpression = dOperand2

  protected[expressions] val dOperand1 : DomainExpression
  protected[expressions] val dOperand2 : DomainExpression
}

object DBinaryBooleanExpression{
  def unapply(dbbe : DBinaryBooleanExpression) : Option[(SourceLocation,BinaryBooleanOperator,DomainExpression,DomainExpression)] =
    Some(dbbe.sl, dbbe.operator,dbbe.operand1,dbbe.operand2)
}

private[silAST] final class DBinaryBooleanExpressionC private[silAST](
                                                     sl: SourceLocation,
                                                     override val operator: BinaryBooleanOperator,
                                                     override val operand1: DomainExpression,
                                                     override val operand2: DomainExpression
                                                     )
  extends BinaryBooleanExpression(sl, operator, operand1,operand2)
  with DBinaryBooleanExpression
{
  override val dSubExpressions: Seq[DomainExpression] = List(operand1,operand2)
  override val dOperand1 = operand1
  override val dOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainPredicateExpression extends DomainPredicateExpression with DomainExpression
{
  override val arguments: DTermSequence = dArguments
  protected[expressions] val dArguments : DTermSequence
}

private[silAST] final class DDomainPredicateExpressionC (
                                                        sl: SourceLocation,
                                                        override val predicate: DomainPredicate,
                                                        override val arguments: DTermSequence
                                                        )
  extends DomainPredicateExpression(sl, predicate, arguments)
  with DDomainPredicateExpression
  with AtomicExpression
{
  override val dArguments = arguments
  override val dSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DQuantifierExpression private[silAST](
                                                   sl: SourceLocation,
                                                   override val quantifier: Quantifier,
                                                   override val variable: BoundVariable,
                                                   override val expression: DomainExpression
                                                   )
  extends QuantifierExpression(sl, quantifier, variable, expression)
  with DomainExpression
{
  override val subExpressions: Seq[DomainExpression] = List(expression)
  override val dSubExpressions = subExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//General/ground
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait GeneralExpression
  extends Expression with DomainExpression with ProgramExpression
{
  override val subExpressions: Seq[GeneralExpression] = gSubExpressions
  protected[expressions] final override val pSubExpressions = subExpressions
  protected[expressions] final override val dSubExpressions = subExpressions

  protected[expressions] val gSubExpressions: Seq[GeneralExpression]
}

///////////////////////////////////////////////////////////////////////////
final class GEqualityExpression private[silAST] (
                                                 sl: SourceLocation,
                                                 override val term1: GeneralTerm,
                                                 override val term2: GeneralTerm
                                                 )
  extends EqualityExpression(sl, term1, term2)
  with PEqualityExpression with DEqualityExpression with GeneralExpression
{
  override val subExpressions : Seq[GeneralExpression] = Nil
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pTerm1 = term1
  protected[expressions] override val pTerm2 = term2
  protected[expressions] override val dTerm1 = term1
  protected[expressions] override val dTerm2 = term2
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GUnaryBooleanExpression private[silAST](
   sl: SourceLocation,
   operator: UnaryBooleanOperator,
   override val operand1: GeneralExpression
  ) extends UnaryBooleanExpression(sl,operator,operand1)
  with PUnaryBooleanExpression
  with DUnaryBooleanExpression
  with GeneralExpression
{
  override val subNodes = List(operator,operand1)

  override val subExpressions = List(operand1)
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GBinaryBooleanExpression private[silAST](
    sl: SourceLocation,
    operator: BinaryBooleanOperator,
    override val operand1: GeneralExpression,
    override val operand2: GeneralExpression
    ) extends BinaryBooleanExpression(sl,operator,operand1,operand2)
  with PBinaryBooleanExpression
  with DBinaryBooleanExpression
  with GeneralExpression
{

  override val subNodes = List(operand1,operator,operand2)

  override val subExpressions = List(operand1,operand2)

  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1
  protected[expressions] override val pOperand2 = operand2
  protected[expressions] override val dOperand2 = operand2
}
