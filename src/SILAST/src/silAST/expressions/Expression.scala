package silAST.expressions

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation
import silAST.expressions.permission.PermissionTerm
import silAST.expressions.terms.Term
import silAST.symbols.logical.BinaryBooleanOperator
import silAST.symbols.logical.UnaryBooleanOperator

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression(sl : SourceLocation) extends ASTNode(sl)
 {
  def subExpressions : Seq[Expression] 
}

case class AccessPermissionExpression( 
		sl : SourceLocation,
		val reference : Term,
		val permission : PermissionTerm
	) 
	extends Expression(sl) with AtomicExpression
{
  override def toString : String = "acc(" + reference.toString() + "," + permission.toString() + ")"
  override def subNodes : Seq[ASTNode] = return reference :: (permission :: List.empty[ASTNode])
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
trait AtomicExpression extends Expression {
  override def subExpressions = Nil
  
  def subTerms : Seq[Term]
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
case class EqualityExpression(
		sl : SourceLocation, 
		val term1 : Term,
		val term2 : Term
    )
    extends Expression(sl) 
	with AtomicExpression
//    with DomainExpression[T] 
//    with ProgramExpression[T] 
{

  override def toString : String = term1.toString + "=" + term2.toString

  override def subNodes : Seq[ASTNode] = term1 :: term2 :: Nil
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
