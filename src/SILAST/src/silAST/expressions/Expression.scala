package silAST.expressions

import scala.collection.Seq

import silAST.expressions.terms.permission.PermissionTerm
import silAST.expressions.terms.{Term, ProgramTerm, DomainTerm}
import silAST.source.SourceLocation
import silAST.symbols.logical.quantification.{Quantifier, BoundVariable}
import silAST.symbols.logical.{UnaryBooleanOperator, BinaryBooleanOperator}
import silAST.ASTNode

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression(sl : SourceLocation) extends ASTNode(sl)
 {
  def subExpressions : Seq[Expression] 
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
trait AtomicExpression extends Expression {
  override def subExpressions = Nil
  
  def subTerms : Seq[Term]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class AccessPermissionExpression( 
		sl : SourceLocation,
		val reference : Term,
		val permission : PermissionTerm
	) 
	extends Expression(sl) with AtomicExpression
{
  override def toString : String = "acc(" + reference.toString() + "," + permission.toString() + ")"
  override def subNodes : Seq[ASTNode] = return reference :: (permission :: List.empty[ASTNode])
  override def subTerms : Seq[Term] = reference :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class EqualityExpression(
		sl : SourceLocation, 
		val term1 : Term,
		val term2 : Term
    )
    extends Expression(sl) 
	with AtomicExpression
{

  override def toString : String = term1.toString + "=" + term2.toString

  override def subNodes : Seq[ASTNode] = term1 :: term2 :: Nil
  override def subTerms : Seq[Term] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class UnaryBooleanExpression(
		sl : SourceLocation,
		val operator : UnaryBooleanOperator,
		val operand1 : Expression
    )
    extends Expression(sl) {

  override def toString : String = operator.toString + operand1.toString
  override def subNodes: Seq[ASTNode] = operator :: (operand1 :: List.empty[ASTNode])
  override def subExpressions : Seq[Expression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class BinaryBooleanExpression(
		sl : SourceLocation,
		val operator : BinaryBooleanOperator,
		val operand1 : Expression,
		val operand2 : Expression
    )
    extends Expression(sl) 
{

	override def toString : String = operand1.toString + " " + operator.toString + " " + operand2.toString
	
	override def subNodes : Seq[ASTNode] = operand1 :: (operator :: (operand2 :: Nil))
	override def subExpressions: Seq[Expression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class QuantifierExpression(
		sl : SourceLocation,
		val quantifier : Quantifier,
		val variable   : BoundVariable,
		val expression : Expression
    )
	extends Expression(sl) 
{
  override def toString : String = quantifier.toString + " " + variable.name + " : " + variable.dataType.toString + " :: (" + expression.toString + ")"
  
  override def subNodes : Seq[ASTNode] = quantifier :: variable :: expression :: Nil
  override def subExpressions: Seq[Expression] = expression :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract trait ProgramExpression 
	extends Expression
{
	override def subExpressions: Seq[ProgramExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class PEqualityExpression(
		sl : SourceLocation, 
		override val term1 : ProgramTerm,
		override val term2 : ProgramTerm
    )
    extends EqualityExpression(sl,term1,term2) 
	with ProgramExpression
{
	override def subTerms : Seq[ProgramTerm] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class PUnaryBooleanExpression(
		sl : SourceLocation,
		operator : UnaryBooleanOperator,
		override val operand1 : ProgramExpression
    )
    extends UnaryBooleanExpression(sl,operator,operand1)
	with ProgramExpression
{
	override def subExpressions : Seq[ProgramExpression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class PBinaryBooleanExpression(
		sl : SourceLocation,
		operator : BinaryBooleanOperator,
		override val operand1 : ProgramExpression,
		override val operand2 : ProgramExpression
    )
    extends BinaryBooleanExpression(sl,operator,operand1,operand2)
	with ProgramExpression
{
	override def subExpressions: Seq[ProgramExpression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract trait DomainExpression 
	extends Expression
{
	override def subExpressions: Seq[DomainExpression]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class DEqualityExpression(
		sl : SourceLocation, 
		override val term1 : DomainTerm,
		override val term2 : DomainTerm
    )
    extends EqualityExpression(sl,term1,term2) 
	with DomainExpression
{
	override def subTerms : Seq[DomainTerm] = term1 :: term2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class DUnaryBooleanExpression(
		sl : SourceLocation,
		operator : UnaryBooleanOperator,
		override val operand1 : DomainExpression
    )
    extends UnaryBooleanExpression(sl,operator,operand1)
	with DomainExpression
{
	override def subExpressions : Seq[DomainExpression] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class DBinaryBooleanExpression(
		sl : SourceLocation,
		operator : BinaryBooleanOperator,
		override val operand1 : DomainExpression,
		override val operand2 : DomainExpression
    )
    extends BinaryBooleanExpression(sl,operator,operand1,operand2)
	with DomainExpression
{
	override def subExpressions: Seq[DomainExpression] = operand1 :: operand2 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class DQuantifierExpression(
		sl : SourceLocation,
		quantifier : Quantifier,
		variable   : BoundVariable,
		override val expression : DomainExpression
    )
	extends QuantifierExpression(sl,quantifier,variable,expression)
	with DomainExpression
{
  override def subExpressions: Seq[DomainExpression] = expression :: Nil
}
