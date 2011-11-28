package silAST.expressions.terms

import silAST.expressions.util.{PArgumentSequence, DArgumentSequence, ArgumentSequence}
import silAST.symbols.logical.quantification.BoundVariable
import silAST.symbols.{ProgramVariable, Field, Function}
import silAST.types.DataType
import silAST.{AtomicNode, ASTNode}
import silAST.domains.DomainFunction

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Term extends ASTNode {
	
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
abstract case class DomainFunctionApplicationTerm(
                                                   function : DomainFunction,
      arguments : ArgumentSequence
	) 
	extends Term
{
	assert(function!=null)
	assert(arguments!=null)

	override def toString : String = function.name + arguments.toString

	override def subNodes: Seq[ASTNode] = List(function) ++ arguments.asSeq 
	override def subTerms : Seq[Term] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class FunctionApplicationTerm(
                                             receiver : Term,
      function : Function,
      arguments : ArgumentSequence
	) 
	extends Term
{
	assert(function!=null)
	assert(arguments!=null)
	assert(receiver!=null)

	override def toString : String = receiver.toString + "." + function.name + arguments.toString

	override def subNodes: Seq[ASTNode] = List(receiver,function) ++ arguments.asSeq 
	override def subTerms : Seq[Term] = List(receiver) ++ arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class LiteralTerm() 
	extends Term 
	with AtomicTerm
	with AtomicNode
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class IntegerLiteral(val value:BigInt) 
	extends LiteralTerm 
	with AtomicNode
{
	assert(value!=null)
  
	override def toString : String = value.toString
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
abstract case class BoundVariableTerm(
                                       variable : BoundVariable
	) 
	extends Term
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
abstract case class CastTerm(
                              operand1: Term,
    newType : DataType
    )
    extends Term 
{
	assert(operand1 != null)
	assert(newType  != null)

	override def toString : String = "(" + operand1 + ") : " + newType.toString

	override def subNodes : Seq[ASTNode] = operand1 :: newType :: Nil

	override def subTerms  : Seq[Term] = operand1 :: Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class FieldReadTerm(
                                   location : Term,
    field : Field
    ) 
    extends Term 
{
	assert(location != null)
	assert(field    != null)

	override def toString : String = location.toString + "." + field.name

	override def subNodes : Seq[ASTNode] = location :: field :: Nil
	override def subTerms : Seq[Term]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class OldFieldReadTerm(
                                      location : Term,
    field : Field)
  extends Term 
{
	override def toString : String = location.toString + "._(old)" + field.name

	override def subNodes : Seq[ASTNode] = location :: field :: Nil
	override def subTerms : Seq[Term]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class ProgramVariableTerm(
                                         variable : ProgramVariable
	) 
	extends Term
	with AtomicTerm
{
	assert(variable!=null)
	
	override def toString : String = variable.name
	override def subNodes : Seq[ASTNode] = variable :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class OldProgramVariableTerm(
		variable : ProgramVariable 
	) 
	extends ProgramVariableTerm(variable) 
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
abstract class PLiteralTerm 
	extends LiteralTerm 
	with ProgramTerm
{
	override def subTerms : Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PFunctionApplicationTerm(
	    receiver : Term,
	    function : Function, 
	    arguments : PArgumentSequence
	) 
	extends FunctionApplicationTerm(receiver,function,arguments)
	with ProgramTerm
{
	override def subTerms : Seq[ProgramTerm] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PDomainFunctionApplicationTerm(
		function : DomainFunction, 
		arguments : PArgumentSequence
    )
	extends DomainFunctionApplicationTerm(function,arguments)
	with ProgramTerm
{
	override def subTerms : Seq[ProgramTerm] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PCastTerm(
		override val operand1: ProgramTerm, 
		newType : DataType
    )
    extends CastTerm(operand1, newType) 
	with ProgramTerm 
{
	assert(operand1 != null)

	override def subTerms  : Seq[ProgramTerm] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PFieldReadTerm(
		location : ProgramTerm, 
		field : Field
    ) 
    extends FieldReadTerm(location,field) 
	with ProgramTerm 
{
	override def subTerms : Seq[ProgramTerm]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class POldFieldReadTerm(
		override val location : ProgramTerm, 
		field : Field
	) 
	extends OldFieldReadTerm(location,field)
	with ProgramTerm 
{
	override def subTerms : Seq[ProgramTerm]    = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
abstract class PProgramVariableTerm(
		variable : ProgramVariable
    ) extends ProgramVariableTerm(variable) 
	with ProgramTerm
{
	override def subTerms: Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
abstract class POldProgramVariableTerm(
		variable : ProgramVariable
    ) extends OldProgramVariableTerm(variable) 
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
abstract class DLiteralTerm 
	extends LiteralTerm 
	with DomainTerm
{
	override def subTerms : Seq[DomainTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DDomainFunctionApplicationTerm(
	    function : DomainFunction, 
	    arguments : DArgumentSequence
	) 
	extends DomainFunctionApplicationTerm(function,arguments)
	with DomainTerm
{
	override def subTerms : Seq[DomainTerm] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class DBoundVariableTerm(
		variable : BoundVariable
	)
	extends BoundVariableTerm(variable)
	with DomainTerm
{
	override def subTerms : Seq[DomainTerm] = Nil
}
