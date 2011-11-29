package silAST.expressions.terms

import silAST.expressions.util.{PArgumentSequence, DArgumentSequence, ArgumentSequence}
import silAST.symbols.logical.quantification.BoundVariable
import silAST.symbols.{ProgramVariable, Field, Function}
import silAST.types.DataType
import silAST.{AtomicNode, ASTNode}
import silAST.domains.DomainFunction
import silAST.source.SourceLocation

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Term protected[silAST](sl : SourceLocation) extends ASTNode(sl)
{
  def subTerms: Seq[Term]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
trait AtomicTerm extends Term {
  def subTerms: Seq[Term] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//General terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class DomainFunctionApplicationTerm(
   sl : SourceLocation,
   val function: DomainFunction,
   val arguments: ArgumentSequence
) extends Term(sl)
{
  override def toString: String = function.name + arguments.toString

  override def subNodes: Seq[ASTNode] = List(function) ++ arguments.asSeq

  override def subTerms: Seq[Term] = arguments.asSeq
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FunctionApplicationTerm(
    sl : SourceLocation,
    val receiver: Term,
    val function: Function,
    val arguments: ArgumentSequence
) extends Term(sl)
{
  override def toString: String = receiver.toString + "." + function.name + arguments.toString

  override def subNodes: Seq[ASTNode] = List(receiver, function) ++ arguments.asSeq

  override def subTerms: Seq[Term] = List(receiver) ++ arguments.asSeq
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class LiteralTerm protected[silAST](sl : SourceLocation)
  extends Term(sl)
  with AtomicTerm
  with AtomicNode
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class IntegerLiteral private[silAST](sl : SourceLocation, val value: BigInt)
  extends LiteralTerm(sl)
  with AtomicNode
{
  override def toString: String = value.toString()
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
case class BoundVariableTerm protected[silAST](
  sl : SourceLocation,
  variable: BoundVariable
)  extends Term(sl)
{
  override def toString: String = variable.name

  override def subNodes: Seq[ASTNode] = variable :: Nil

  override def subTerms: Seq[Term] = Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class CastTerm protected[silAST](
  sl : SourceLocation,
  val operand1: Term,
  val newType: DataType
)
  extends Term(sl)
{
  override def toString: String = "(" + operand1 + ") : " + newType.toString

  override def subNodes: Seq[ASTNode] = operand1 :: newType :: Nil

  override def subTerms: Seq[Term] = operand1 :: Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FieldReadTerm protected[silAST](
  sl : SourceLocation,
  val location: Term,
  val field: Field
)
  extends Term(sl)
{

  override def toString: String = location.toString + "." + field.name

  override def subNodes: Seq[ASTNode] = location :: field :: Nil

  override def subTerms: Seq[Term] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class OldFieldReadTerm protected[silAST](
  sl : SourceLocation,
  val location: Term,
  val field: Field
)
  extends Term(sl)
{
  override def toString: String = location.toString + "._(old)" + field.name

  override def subNodes: Seq[ASTNode] = location :: field :: Nil

  override def subTerms: Seq[Term] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract case class ProgramVariableTerm(
  sl : SourceLocation,
  val variable: ProgramVariable
)
extends Term(sl)
  with AtomicTerm
{
  override def toString: String = variable.name

  override def subNodes: Seq[ASTNode] = variable :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class OldProgramVariableTerm protected[silAST](
  sl : SourceLocation,
  override val variable: ProgramVariable
)
  extends ProgramVariableTerm(sl,variable) {
  override def toString: String = "old(" + variable.name + ")"
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
sealed trait ProgramTerm extends Term {
  def subTerms: Seq[ProgramTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class PLiteralTerm(sl : SourceLocation)
  extends LiteralTerm(sl)
  with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFunctionApplicationTerm private[silAST](
                                         sl : SourceLocation,
                                         override val receiver: Term,
                                         override val function: Function,
                                         override val arguments: PArgumentSequence
                                         )
  extends FunctionApplicationTerm(sl, receiver, function, arguments)
  with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = arguments.asSeq

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PDomainFunctionApplicationTerm private[silAST](
                                               sl : SourceLocation,
                                               override val function: DomainFunction,
                                               override val arguments: PArgumentSequence
                                               )
  extends DomainFunctionApplicationTerm(sl, function, arguments)
  with ProgramTerm
{
  override def subTerms: Seq[ProgramTerm] = arguments.asSeq
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PCastTerm private[silAST](
                          sl : SourceLocation,
                          override val operand1: ProgramTerm,
                          override val newType: DataType
                          )
  extends CastTerm(sl,operand1, newType)
  with ProgramTerm
{
  override def subTerms: Seq[ProgramTerm] = operand1 :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFieldReadTerm private[silAST](
                               sl : SourceLocation,
                               override val location: ProgramTerm,
                               override val field: Field
                               )
  extends FieldReadTerm(sl, location, field)
  with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class POldFieldReadTerm private[silAST](
                                  sl : SourceLocation,
                                  override val location: ProgramTerm,
                                  override val field: Field
                                  )
  extends OldFieldReadTerm(sl,location, field)
  with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
final class PProgramVariableTerm private[silAST](
                                     sl :  SourceLocation,
                                     override val variable: ProgramVariable
                                     ) extends ProgramVariableTerm(sl,variable)
with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
final class POldProgramVariableTerm private[silAST](
                                        sl : SourceLocation,
                                        override val variable: ProgramVariable
                                        ) extends OldProgramVariableTerm(sl, variable)
with ProgramTerm {
  override def subTerms: Seq[ProgramTerm] = Nil
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DomainTerm extends Term {
  def subTerms: Seq[DomainTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DLiteralTerm private[silAST](sl : SourceLocation)
  extends LiteralTerm(sl)
  with DomainTerm
{
  override def subTerms: Seq[DomainTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DDomainFunctionApplicationTerm private[silAST](
  sl : SourceLocation,
  override val function: DomainFunction,
  override val arguments: DArgumentSequence
)
  extends DomainFunctionApplicationTerm(sl,function, arguments)
  with DomainTerm
{
  override def subTerms: Seq[DomainTerm] = arguments.asSeq
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DBoundVariableTerm private[silAST](
  sl : SourceLocation,
  override val variable: BoundVariable
)
  extends BoundVariableTerm(sl,variable)
  with DomainTerm
{
  override def subTerms: Seq[DomainTerm] = Nil
}
