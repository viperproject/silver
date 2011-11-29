package silAST.expressions

import scala.collection.Seq

import silAST.domains.DomainPredicate
import silAST.expressions.terms.permission.PermissionTerm
import silAST.expressions.terms.{Term, ProgramTerm, DomainTerm}
import silAST.expressions.util.{PArgumentSequence, DArgumentSequence, ArgumentSequence}
import silAST.symbols.logical.quantification.{Quantifier, BoundVariable}
import silAST.symbols.logical.{UnaryBooleanOperator, BinaryBooleanOperator}
import silAST.symbols.Predicate
import silAST.ASTNode

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression extends ASTNode {
  def subExpressions: Seq[Expression]
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class AccessPermissionExpression(
                                                reference: Term,
                                                permission: PermissionTerm
                                                )
  extends Expression
//  with AtomicExpression
{

  override def toString: String = "acc(" + reference.toString + "," + permission.toString + ")"

  override def subNodes: Seq[ASTNode] = reference :: (permission :: List.empty[ASTNode])

//  override def subTerms: Seq[Term] = reference :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class UnfoldingExpression(
                                         predicate: Term,
                                         expression: Expression
                                         ) extends Expression {
  override def toString: String = "unfolding " + predicate.toString + " in " + expression.toString

  override def subNodes: Seq[ASTNode] = List(predicate, expression)

  override def subExpressions: Seq[Expression] = List(expression)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class EqualityExpression(
                                        term1: Term,
                                        term2: Term
                                        )
  extends Expression
//  with AtomicExpression
{

  override def toString: String = term1.toString + "=" + term2.toString

  override def subNodes: Seq[ASTNode] = term1 :: term2 :: Nil

//  override def subTerms: Seq[Term] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class UnaryBooleanExpression(
                                            operator: UnaryBooleanOperator,
                                            operand1: Expression
                                            ) extends Expression {
  override def toString: String = operator.toString + operand1.toString

  override def subNodes: Seq[ASTNode] = operator :: (operand1 :: List.empty[ASTNode])

  override def subExpressions: Seq[Expression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class BinaryBooleanExpression(
                                             operator: BinaryBooleanOperator,
                                             operand1: Expression,
                                             operand2: Expression
                                             ) extends Expression {
  override def toString: String = operand1.toString + " " + operator.toString + " " + operand2.toString

  override def subNodes: Seq[ASTNode] = operand1 :: (operator :: (operand2 :: Nil))

  override def subExpressions: Seq[Expression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class DomainPredicateExpression(
                                               predicate: DomainPredicate,
                                               arguments: ArgumentSequence
                                               )
  extends Expression
//  with AtomicExpression
{
  override def toString: String = predicate.name + arguments.toString

  override def subNodes: Seq[ASTNode] = predicate :: arguments.asSeq.asInstanceOf[List[ASTNode]]

//  override def subTerms: Seq[Term] = arguments.asSeq
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class PredicateExpression(
                                         receiver: Term,
                                         predicate: Predicate
                                         )
  extends Expression
//  with AtomicExpression
{

  override def toString: String = receiver + "." + predicate.name

  override def subNodes: Seq[ASTNode] = List(receiver, predicate)

//  override def subTerms: Seq[Term] = List(receiver)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class QuantifierExpression(
                                          quantifier: Quantifier,
                                          variable: BoundVariable,
                                          expression: Expression
                                          )
  extends Expression {
  override def toString: String = quantifier.toString + " " + variable.name + " : " + variable.dataType.toString + " :: (" + expression.toString + ")"

  override def subNodes: Seq[ASTNode] = quantifier :: variable :: expression :: Nil

  override def subExpressions: Seq[Expression] = expression :: Nil
}
sealed trait AtomicExpression extends Expression {
  override def subExpressions = Nil

  def subTerms: Seq[Term]
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
sealed abstract trait ProgramExpression
  extends Expression {
  override def subExpressions: Seq[ProgramExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PEqualityExpression(
                                    override val term1: ProgramTerm,
                                    override val term2: ProgramTerm
                                    )
  extends EqualityExpression(term1, term2)
  with ProgramExpression
{
//  override def subTerms: Seq[ProgramTerm] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PUnaryBooleanExpression(
                                        override val operator: UnaryBooleanOperator,
                                        override val operand1: ProgramExpression
                                        )
  extends UnaryBooleanExpression(operator, operand1)
  with ProgramExpression {
  override def subExpressions: Seq[ProgramExpression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PBinaryBooleanExpression(
                                         override val operator: BinaryBooleanOperator,
                                         override val operand1: ProgramExpression,
                                         override val operand2: ProgramExpression
                                         )
  extends BinaryBooleanExpression(operator, operand1, operand2)
  with ProgramExpression {
  override def subExpressions: Seq[ProgramExpression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PPredicateExpression(
                                     override val receiver: ProgramTerm,
                                     override val predicate: Predicate
                                     )
  extends PredicateExpression(receiver, predicate)
  with ProgramExpression
{
//  override def subTerms: Seq[ProgramTerm] = List(receiver)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PDomainPredicateExpression(
                                           override val predicate: DomainPredicate,
                                           override val arguments: PArgumentSequence
                                           )
  extends DomainPredicateExpression(predicate, arguments)
  with ProgramExpression
{
  //  override def subTerms: Seq[ProgramTerm] = arguments.asSeq
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract trait DomainExpression
  extends Expression {
  override def subExpressions: Seq[DomainExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DEqualityExpression(
                                    override val term1: DomainTerm,
                                    override val term2: DomainTerm
                                    )
  extends EqualityExpression(term1, term2)
  with DomainExpression
{
//  override def subTerms: Seq[DomainTerm] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DUnaryBooleanExpression(
                                        override val operator: UnaryBooleanOperator,
                                        override val operand1: DomainExpression
                                        )
  extends UnaryBooleanExpression(operator, operand1)
  with DomainExpression {
  override def subExpressions: Seq[DomainExpression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DBinaryBooleanExpression(
                                         override val operator: BinaryBooleanOperator,
                                         override val operand1: DomainExpression,
                                         override val operand2: DomainExpression
                                         )
  extends BinaryBooleanExpression(operator, operand1, operand2)
  with DomainExpression {
  override def subExpressions: Seq[DomainExpression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DQuantifierExpression(
                                      override val quantifier: Quantifier,
                                      override val variable: BoundVariable,
                                      override val expression: DomainExpression
                                      )
  extends QuantifierExpression(quantifier, variable, expression)
  with DomainExpression {
  override def subExpressions: Seq[DomainExpression] = expression :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DDomainPredicateExpression(
                                           override val predicate: DomainPredicate,
                                           override val arguments: DArgumentSequence
                                           )
  extends DomainPredicateExpression(predicate, arguments)
  with DomainExpression
{
//  override def subTerms: Seq[DomainTerm] = arguments.asSeq
}
