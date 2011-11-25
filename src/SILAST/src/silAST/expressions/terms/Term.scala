package silAST.expressions.terms
import silAST.source.SourceLocation
import silAST.ASTNode
import silAST.symbols.Function
import silAST.symbols.ArgumentSequence
import silAST.symbols.DataType
import silAST.symbols.Field
import silAST.symbols.ProgramVariable
import silAST.symbols.logical.quantification.BoundVariable
import silAST.AtomicNode
import silAST.symbols.PArgumentSequence
import silAST.symbols.DArgumentSequence

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Term(sl : SourceLocation) extends ASTNode(sl) {
	assert(sl!=null)
	
	def subTerms: Seq[Term]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
trait AtomicTerm extends Term {
  def subTerms : Seq[Term] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//General terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FunctionApplicationTerm(
	    sl:SourceLocation,
	    val function : Function, 
	    val arguments : ArgumentSequence
	) 
	extends Term(sl)
{
	assert(function!=null)
	assert(arguments!=null)

	override def toString : String = function.name + arguments.toString

	override def subNodes: Seq[ASTNode] = List(function) ++ arguments.asSeq 
	override def subTerms : Seq[Term] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class LiteralTerm(sl:SourceLocation) 
	extends Term(sl) 
	with AtomicTerm
	with AtomicNode
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class IntegerLiteral( sl : SourceLocation, val value:BigInt) 
	extends LiteralTerm(sl) 
	with AtomicNode
{
	assert(value!=null)
  
	override def toString : String = value.toString()
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
case class BoundVariableTerm(
		sl : SourceLocation, 
		val variable : BoundVariable 
	) 
	extends Term(sl)
{
	assert(variable!=null);
	
	override def toString : String = variable.name
	override def subNodes : Seq[ASTNode] = variable :: Nil
	
	override def subTerms : Seq[Term] = Nil
	
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class CastTerm(
		sl:SourceLocation, 
		val operand1: Term, 
		val newType : DataType
    )
    extends Term(sl) 
{
	assert(operand1 != null)
	assert(newType  != null)

	override def toString : String = "(" + operand1 + ") : " + newType.toString

	override def subNodes : Seq[ASTNode] = operand1 :: newType :: Nil

	override def subTerms  : Seq[Term] = operand1 :: Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FieldReadTerm(
		sl : SourceLocation, 
		val location : Term, 
		val field : Field
    ) 
    extends Term(sl) 
{
	assert(location != null)
	assert(field    != null)

	override def toString : String = location.toString() + "." + field.name

	override def subNodes : Seq[ASTNode] = location :: field :: Nil
	override def subTerms : Seq[Term]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class OldFieldReadTerm(
    sl : SourceLocation, 
    val location : Term, 
    val field : Field) 
  extends Term(sl) 
{
	override def toString : String = location.toString() + "._(old)" + field.name

	override def subNodes : Seq[ASTNode] = location :: field :: Nil
	override def subTerms : Seq[Term]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class ProgramVariableTerm(
		sl : SourceLocation, 
		val variable : ProgramVariable 
	) 
	extends Term(sl)
	with AtomicTerm
{
	assert(variable!=null)
	
	override def toString : String = variable.name
	override def subNodes : Seq[ASTNode] = variable :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class OldProgramVariableTerm(
		sl : SourceLocation, 
		variable : ProgramVariable 
	) 
	extends ProgramVariableTerm(sl, variable) 
{
	override def toString : String = "old(" + variable.name + ")"
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
abstract sealed trait ProgramTerm extends Term
{
	def subTerms: Seq[ProgramTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PLiteralTerm(sl:SourceLocation) 
	extends LiteralTerm(sl) 
	with ProgramTerm
{
	override def subTerms : Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class PFunctionApplicationTerm(
	    sl:SourceLocation,
	    function : Function, 
	    arguments : PArgumentSequence
	) 
	extends FunctionApplicationTerm(sl,function,arguments)
	with ProgramTerm
{
	override def subTerms : Seq[ProgramTerm] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class PCastTerm(
		sl:SourceLocation, 
		override val operand1: ProgramTerm, 
		newType : DataType
    )
    extends CastTerm(sl,operand1, newType) 
	with ProgramTerm 
{
	assert(operand1 != null)

	override def subTerms  : Seq[ProgramTerm] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class PFieldReadTerm(
		sl : SourceLocation, 
    	override val location : ProgramTerm, 
    	field : Field
    ) 
    extends FieldReadTerm(sl,location,field) 
	with ProgramTerm 
{
	override def subTerms : Seq[ProgramTerm]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class POldFieldReadTerm(
		sl : SourceLocation, 
		override val location : ProgramTerm, 
		field : Field
	) 
	extends OldFieldReadTerm(sl,location,field)
	with ProgramTerm 
{
	override def subTerms : Seq[ProgramTerm]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
class PProgramVariableTerm(
		override val sl : SourceLocation,
		override val variable : ProgramVariable
    ) extends ProgramVariableTerm(sl,variable) 
	with ProgramTerm
{
	override def subTerms: Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
class POldProgramVariableTerm(
		override val sl : SourceLocation,
		override val variable : ProgramVariable
    ) extends OldProgramVariableTerm(sl,variable) 
	with ProgramTerm
{
	override def subTerms: Seq[ProgramTerm] = Nil
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract sealed trait DomainTerm extends Term
{
	def subTerms: Seq[DomainTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DLiteralTerm(sl:SourceLocation) 
	extends LiteralTerm(sl) 
	with DomainTerm
{
	override def subTerms : Seq[DomainTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class DFunctionApplicationTerm(
	    sl:SourceLocation,
	    function : Function, 
	    arguments : DArgumentSequence
	) 
	extends FunctionApplicationTerm(sl,function,arguments)
	with DomainTerm
{
	override def subTerms : Seq[DomainTerm] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class DBoundVariableTerm(
		sl : SourceLocation, 
		variable : BoundVariable 
	) 
	extends BoundVariableTerm(sl,variable)
	with DomainTerm
{
	override def subTerms : Seq[DomainTerm] = Nil
}
