package silAST.expressions

import scala.collection.Seq

import silAST.domains.DomainPredicate
import silAST.expressions.terms.permission.PermissionTerm
import terms.{Term, ProgramTerm, DomainTerm}
import silAST.expressions.util.{TermSequence,PTermSequence, DTermSequence}
import silAST.symbols.logical.quantification.{Quantifier, BoundVariable}
import silAST.symbols.logical.{UnaryBooleanOperator, BinaryBooleanOperator}
import silAST.symbols.Predicate
import silAST.ASTNode
import silAST.source.SourceLocation

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression protected[silAST](
  sl : SourceLocation
)extends ASTNode(sl)
{
  def subExpressions: Seq[Expression]
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class AccessPermissionExpression private[silAST](
  sl : SourceLocation,
  reference: Term,
  permission: PermissionTerm
)
  extends Expression(sl)
  with AtomicExpression
{

  override def toString = "acc(" + reference.toString + "," + permission.toString + ")"

  override def subNodes = reference :: (permission :: List.empty[ASTNode])
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class UnfoldingExpression private[silAST](
  sl : SourceLocation,
  predicate: Term,
  expression: Expression
) extends Expression(sl)
{
  override def toString: String = "unfolding " + predicate.toString + " in " + expression.toString

  override def subNodes: Seq[ASTNode] = List(predicate, expression)

  override def subExpressions: Seq[Expression] = List(expression)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class EqualityExpression private[silAST](
    sl : SourceLocation,
    term1: Term,
    term2: Term
)
  extends Expression(sl)
  with AtomicExpression
{

  override def toString: String = term1.toString + "=" + term2.toString

  override def subNodes: Seq[ASTNode] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class UnaryBooleanExpression private[silAST](
    sl : SourceLocation,
    operator: UnaryBooleanOperator,
    operand1: Expression
) extends Expression(sl)
{
  override def toString: String = operator.toString + operand1.toString

  override def subNodes: Seq[ASTNode] = operator :: (operand1 :: List.empty[ASTNode])

  override def subExpressions: Seq[Expression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class BinaryBooleanExpression private[silAST](
  sl : SourceLocation,
  operator: BinaryBooleanOperator,
  operand1: Expression,
  operand2: Expression
) extends Expression(sl)
{
  override def toString: String = operand1.toString + " " + operator.toString + " " + operand2.toString

  override def subNodes: Seq[ASTNode] = operand1 :: (operator :: (operand2 :: Nil))

  override def subExpressions: Seq[Expression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class DomainPredicateExpression private[silAST](
  sl : SourceLocation,
  predicate: DomainPredicate,
  arguments: TermSequence
) extends Expression(sl)
  with AtomicExpression
{
  override def toString: String = predicate.name + arguments.toString

  override def subNodes: Seq[ASTNode] = predicate :: arguments.asInstanceOf[List[ASTNode]]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class PredicateExpression private[silAST](
  sl : SourceLocation,
  receiver: Term,
 predicate: Predicate
) extends Expression(sl)
  with AtomicExpression
{

  override def toString: String = receiver + "." + predicate.name

  override def subNodes: Seq[ASTNode] = List(receiver, predicate)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class QuantifierExpression private[silAST](
    sl : SourceLocation,
    quantifier: Quantifier,
    variable: BoundVariable,
    expression: Expression
)
  extends Expression(sl)
{
  override def toString: String = quantifier.toString + " " + variable.name + " : " + variable.dataType.toString + " :: (" + expression.toString + ")"

  override def subNodes: Seq[ASTNode] = quantifier :: variable :: expression :: Nil

  override def subExpressions: Seq[Expression] = expression :: Nil
}

sealed trait AtomicExpression extends Expression {
  override def subExpressions = Nil
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
  extends Expression {
  override def subExpressions: Seq[ProgramExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PEqualityExpression private[silAST](
  sl : SourceLocation,
  override val term1: ProgramTerm,
  override val term2: ProgramTerm
)
  extends EqualityExpression(sl, term1, term2)
  with ProgramExpression
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnaryBooleanExpression private[silAST](
  sl : SourceLocation,
  override val operator: UnaryBooleanOperator,
  override val operand1: ProgramExpression
)
  extends UnaryBooleanExpression(sl, operator, operand1)
  with ProgramExpression
{
  override def subExpressions: Seq[ProgramExpression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PBinaryBooleanExpression private[silAST](
  sl : SourceLocation,
  override val operator: BinaryBooleanOperator,
  override val operand1: ProgramExpression,
  override val operand2: ProgramExpression
)
  extends BinaryBooleanExpression(sl, operator, operand1, operand2)
  with ProgramExpression
{
  override def subExpressions: Seq[ProgramExpression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PPredicateExpression private[silAST](
  sl : SourceLocation,
  override val receiver: ProgramTerm,
  override val predicate: Predicate
)
  extends PredicateExpression(sl,receiver, predicate)
  with ProgramExpression
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PDomainPredicateExpression private[silAST](
  sl : SourceLocation,
  override val predicate: DomainPredicate,
  override val arguments: PTermSequence
)
  extends DomainPredicateExpression(sl, predicate, arguments)
  with ProgramExpression
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DomainExpression
  extends Expression
{
  override def subExpressions: Seq[DomainExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DEqualityExpression private[silAST](
  sl : SourceLocation,
  override val term1: DomainTerm,
  override val term2: DomainTerm
)
  extends EqualityExpression(sl,term1, term2)
  with DomainExpression
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DUnaryBooleanExpression private[silAST](
  sl : SourceLocation,
  override val operator: UnaryBooleanOperator,
  override val operand1: DomainExpression
) extends UnaryBooleanExpression(sl, operator, operand1)
  with DomainExpression
{
  override def subExpressions: Seq[DomainExpression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DBinaryBooleanExpression(
     sl : SourceLocation,
     override val operator: BinaryBooleanOperator,
     override val operand1: DomainExpression,
     override val operand2: DomainExpression
)
  extends BinaryBooleanExpression(sl, operator, operand1, operand2)
  with DomainExpression
{
  override def subExpressions: Seq[DomainExpression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DQuantifierExpression private[silAST](
  sl : SourceLocation,
  override val quantifier: Quantifier,
  override val variable: BoundVariable,
  override val expression: DomainExpression
)
  extends QuantifierExpression(sl, quantifier, variable, expression)
  with DomainExpression {
  override def subExpressions: Seq[DomainExpression] = expression :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DDomainPredicateExpression  private[silAST](
  sl : SourceLocation,
  override val predicate: DomainPredicate,
  override val arguments: DTermSequence
)
  extends DomainPredicateExpression(sl,predicate, arguments)
  with DomainExpression
{
}
