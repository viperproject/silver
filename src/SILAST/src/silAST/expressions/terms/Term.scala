package silAST.expressions.terms

import silAST.symbols.logical.quantification.BoundVariable
import silAST.symbols.{ProgramVariable, Field, Function}
import silAST.types.DataType
import silAST.{AtomicNode, ASTNode}
import silAST.domains.DomainFunction
import silAST.source.SourceLocation
import silAST.expressions.util.{DTermSequence, PTermSequence, TermSequence}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait Term extends ASTNode
{
  def subTerms: Seq[Term]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait AtomicTerm extends Term {
  final override def subTerms = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Assertion terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationTerm private[silAST](
   sl : SourceLocation,
   function: DomainFunction,
   arguments: TermSequence
) extends ASTNode(sl) with Term
{
  override val toString = function.name + arguments.toString

  override val subNodes = List(function) ++ arguments

  override val subTerms  = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FunctionApplicationTerm protected[silAST](
    sl : SourceLocation,
    receiver: Term,
    function: Function,
    arguments: TermSequence
) extends ASTNode(sl) with Term
{
  override def toString: String = receiver.toString + "." + function.name + arguments.toString

  override def subNodes: Seq[ASTNode] = List(receiver, function) ++ arguments

  override def subTerms: Seq[Term] = List(receiver) ++ arguments.toList
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class BoundVariableTerm protected[silAST](
    sl : SourceLocation,
    variable: BoundVariable
  )
  extends ASTNode(sl)
  with DomainTerm
{
  override val toString  = variable.name

  override val subNodes = List(variable)

  override val dSubTerms = Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class CastTerm protected[silAST](
  sl : SourceLocation,
  operand1: Term,
  newType: DataType
)
  extends ASTNode(sl) with Term
{
  override def toString: String = "(" + operand1 + ") : " + newType.toString

  override def subNodes: Seq[ASTNode] = operand1 :: newType :: Nil

  override def subTerms: Seq[Term] = operand1 :: Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldReadTerm protected[silAST](
  sl : SourceLocation,
  location: Term,
  field: Field
)
  extends ASTNode(sl) with Term
{

  override def toString: String = location.toString + "." + field.name

  override def subNodes: Seq[ASTNode] = location :: field :: Nil

  override def subTerms: Seq[Term] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class OldFieldReadTerm protected[silAST](
  sl : SourceLocation,
  location: Term,
  field: Field
)
  extends ASTNode(sl) with Term
{
  override def toString: String = location.toString + "._(old)" + field.name

  override def subNodes: Seq[ASTNode] = location :: field :: Nil

  override def subTerms: Seq[Term] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableTerm protected[silAST](
  sl : SourceLocation,
  variable: ProgramVariable
)
  extends ASTNode(sl)
  with ProgramTerm
  with AtomicTerm
{
  override def toString: String = variable.name

  override def subNodes: Seq[ASTNode] = List(variable)

  override val pSubTerms = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class OldProgramVariableTerm protected[silAST](
  sl : SourceLocation,
  override val variable: ProgramVariable
)
  extends ProgramVariableTerm(sl,variable) {
  override def toString = "old(" + variable.name + ")"
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
sealed trait ProgramTerm extends Term {
  override def subTerms: Seq[ProgramTerm] = pSubTerms
  protected val pSubTerms : Seq[ProgramTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PFunctionApplicationTerm
  extends FunctionApplicationTerm
  with ProgramTerm
{
  override val receiver  : ProgramTerm = pReceiver
  override val arguments : PTermSequence = pArguments

  protected val pReceiver : ProgramTerm
  protected val pArguments : PTermSequence
}

object PFunctionApplicationTerm {
  def unapply(t : PFunctionApplicationTerm) : Option[(SourceLocation,ProgramTerm,Function,PTermSequence)] =
    Some((t.sl,  t.receiver,t.function,t.arguments))
}

final private[silAST] class PFunctionApplicationTermC (
       sl : SourceLocation,
       override val receiver: ProgramTerm,
       override val function: Function,
       override val arguments: PTermSequence
  )
  extends FunctionApplicationTerm(sl, receiver, function, arguments)
  with PFunctionApplicationTerm
{
//  override def subTerms: Seq[ProgramTerm] = arguments
  override val pSubTerms : Seq[ProgramTerm] = List(receiver) ++ arguments
  override val pArguments =arguments
  override val pReceiver = receiver
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with ProgramTerm
{
  override val arguments : PTermSequence = pArguments

  protected val pArguments : PTermSequence
}

object PDomainFunctionApplicationTerm {
  def unapply(t : PDomainFunctionApplicationTerm) : Option[(SourceLocation,DomainFunction,PTermSequence)] =
    Some((t.sl,t.function,t.arguments))
}

private[silAST] final class PDomainFunctionApplicationTermC(
     sl : SourceLocation,
     override val function: DomainFunction,
     override val arguments: PTermSequence
   )
  extends DomainFunctionApplicationTerm(sl, function, arguments)
  with ProgramTerm
{
  override val pSubTerms = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PCastTerm
  extends CastTerm
  with ProgramTerm
{
  override val operand1 : ProgramTerm = pOperand1
  protected val pOperand1 : ProgramTerm
}

object PCastTerm {
  def unapply(t : PCastTerm) : Option[(SourceLocation,ProgramTerm,DataType)] =
    Some((t.sl,t.operand1,t.newType))
}

private[silAST] final class PCastTermC(
                          sl : SourceLocation,
                          override val operand1: ProgramTerm,
                          override val newType: DataType
                          )
  extends CastTerm(sl,operand1, newType)
  with ProgramTerm
{
  override val pSubTerms: Seq[ProgramTerm] = List(operand1)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PFieldReadTerm
  extends FieldReadTerm
  with ProgramTerm
{
  override val location: ProgramTerm = pLocation
  protected val pLocation : ProgramTerm
}

object PFieldReadTerm {
  def unapply(t : PFieldReadTerm) : Option[(SourceLocation,ProgramTerm,Field)] =
    Some((t.sl,t.location,t.field))
}

private[silAST] final class PFieldReadTermC (
     sl : SourceLocation,
     location: ProgramTerm,
     field: Field
  )
  extends FieldReadTerm(sl, location, field)
  with PFieldReadTerm
{
  override val pSubTerms: Seq[ProgramTerm] = List(location)
  override val pLocation = location
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait POldFieldReadTerm
  extends OldFieldReadTerm
  with ProgramTerm
{
  override val location: ProgramTerm = pLocation
  protected val pLocation : ProgramTerm
}

object POldFieldReadTerm {
  def unapply(t : POldFieldReadTerm) : Option[(SourceLocation,ProgramTerm,Field)] =
    Some((t.sl,t.location,t.field))
}

private[silAST] final class POldFieldReadTermC (
     sl : SourceLocation,
     location: ProgramTerm,
     field: Field
  )
  extends OldFieldReadTerm(sl, location, field)
  with POldFieldReadTerm
{
  override val pSubTerms: Seq[ProgramTerm] = List(location)
  override val pLocation = location
}
/*
///////////////////////////////////////////////////////////////////////////
sealed trait PProgramVariableTerm
  extends OldFieldReadTerm
  with ProgramTerm
{
  override val location: ProgramTerm = pLocation
  protected val pLocation : ProgramTerm
}

object POldFieldReadTerm {
  def unapply(t : POldFieldReadTerm) : Option[(SourceLocation,ProgramTerm,Field)] =
    Some((t.sl,t.location,t.field))
}

private[silAST] final class PProgramVariableTermC(
         sl :  SourceLocation,
         variable: ProgramVariable
     ) extends ProgramVariableTerm(sl,variable)
with ProgramTerm {
  override def pSubTerms: Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
private[silAST] final class POldProgramVariableTerm(
                                        sl : SourceLocation,
                                        override val variable: ProgramVariable
                                        ) extends OldProgramVariableTerm(sl, variable)
with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = Nil
}
*/

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DomainTerm extends Term {
  override def subTerms : Seq[DomainTerm] = dSubTerms
  val dSubTerms : Seq[DomainTerm]
}
/*
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DLiteralTerm private[silAST](sl : SourceLocation)
  extends LiteralTerm(sl)
  with DomainTerm
{
  override def subTerms: Seq[DomainTerm] = Nil
}
*/
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with DomainTerm
{
  override val arguments: DTermSequence = dArguments
  protected val dArguments : DTermSequence
}

object DDomainFunctionApplicationTerm
{
  def unapply(t : DDomainFunctionApplicationTerm) : Option[(SourceLocation,DomainFunction, DTermSequence)] =
    Some((t.sl,t.function,t.arguments))
}


private[silAST] final class DDomainFunctionApplicationTermC(
  sl : SourceLocation,
  function: DomainFunction,
  arguments: DTermSequence
)
  extends DomainFunctionApplicationTerm(sl,function, arguments)
  with DomainTerm
{
  override val dSubTerms = arguments
}
/*
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DBoundVariableTerm private[silAST](
  sl : SourceLocation,
  override val variable: BoundVariable
)
  extends BoundVariableTerm(sl,variable)
  with DomainTerm
{
  override val dSubTerms = Nil
}
*/
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains + Programs = General

///////////////////////////////////////////////////////////////////////////
/*object GeneralTerm{
  type GeneralTerm = Term with DomainTerm with ProgramTerm
}
*/
sealed trait GeneralTerm extends Term with DomainTerm with ProgramTerm{
  val subTerms : Seq[GeneralTerm] = gSubTerms

  private override val dSubTerms = gSubTerms
  private override val pSubTerms = gSubTerms
  protected val gSubTerms : Seq[GeneralTerm]
}

/*final private[silAST] class GIntegerLiteralTerm(sl : SourceLocation, v : BigInt)
  extends IntegerLiteralTerm(sl,v)
  with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = Nil
}
  */

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract case class LiteralTerm protected[silAST](sl : SourceLocation)
  extends ASTNode(sl) with Term
  with GeneralTerm
  with AtomicTerm
  with AtomicNode
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class IntegerLiteralTerm private[silAST](sl : SourceLocation, val value: BigInt)
  extends LiteralTerm(sl)
  with GeneralTerm
  with AtomicNode
{
  override def toString: String = value.toString()
  override def subTerms = Nil //Seq[ProgramTerm] = Nil
}

