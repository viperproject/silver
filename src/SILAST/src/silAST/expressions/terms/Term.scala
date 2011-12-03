package silAST.expressions.terms

import silAST.symbols.logical.quantification.BoundVariable
import silAST.symbols.{ProgramVariable, Field, Function}
import silAST.types.DataType
import silAST.{AtomicNode, ASTNode}
import silAST.domains.DomainFunction
import silAST.source.SourceLocation
import silAST.expressions.util.{GTermSequence, DTermSequence, PTermSequence, TermSequence}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait Term extends ASTNode {
  val subTerms: Seq[Term]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait AtomicTerm extends Term {
  final override val subTerms = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Assertion terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationTerm private[silAST](
                                                                 sl: SourceLocation,
                                                                 function: DomainFunction,
                                                                 arguments: TermSequence
                                                                 ) extends ASTNode(sl) with Term {
  override val toString: String = function.name + arguments.toString

  override val subNodes: Seq[ASTNode] = List(function) ++ arguments

  override val subTerms: Seq[Term] = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FunctionApplicationTerm private[silAST](
                                                           sl: SourceLocation,
                                                           receiver: Term,
                                                           function: Function,
                                                           arguments: TermSequence
                                                           ) extends ASTNode(sl) with Term {
  override val toString: String = receiver.toString + "." + function.name + arguments.toString

  override val subNodes: Seq[ASTNode] = List(receiver, function) ++ arguments

  override val subTerms: Seq[Term] = List(receiver) ++ arguments.toList
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class CastTerm protected[silAST](
                                              sl: SourceLocation,
                                              operand1: Term,
                                              newType: DataType
                                              )
  extends ASTNode(sl) with Term {
  override val toString: String = "(" + operand1 + ") : " + newType.toString

  override val subNodes: Seq[ASTNode] = operand1 :: newType :: Nil

  override val subTerms: Seq[Term] = operand1 :: Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldReadTerm protected[silAST](
                                                   sl: SourceLocation,
                                                   location: Term,
                                                   field: Field
                                                   )
  extends ASTNode(sl) with Term {

  override val toString: String = location.toString + "." + field.name

  override val subNodes: Seq[ASTNode] = location :: field :: Nil

  override val subTerms: Seq[Term] = location :: Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class OldFieldReadTerm protected[silAST](
                                                      sl: SourceLocation,
                                                      location: Term,
                                                      field: Field
                                                      )
  extends ASTNode(sl) with Term {
  override val toString: String = location.toString + "._(old)" + field.name

  override val subNodes: Seq[ASTNode] = location :: field :: Nil

  override val subTerms: Seq[Term] = location :: Nil
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
sealed trait PTerm extends Term {
  override val subTerms: Seq[PTerm] = pSubTerms
  protected val pSubTerms: Seq[PTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableTerm protected[silAST](
                                                         sl: SourceLocation,
                                                         variable: ProgramVariable
                                                         )
  extends ASTNode(sl)
  with PTerm
  with AtomicTerm {
  override val toString: String = variable.name

  override val subNodes: Seq[ASTNode] = List(variable)

  override val pSubTerms = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class OldProgramVariableTerm protected[silAST](
                                                      sl: SourceLocation,
                                                      override val variable: ProgramVariable
                                                      )
  extends ProgramVariableTerm(sl, variable) {
  override val toString = "old(" + variable.name + ")"
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFunctionApplicationTerm private[silAST] (
                                                       sl: SourceLocation,
                                                       override val receiver: PTerm,
                                                       function: Function,
                                                       override val arguments: PTermSequence
                                                       )
  extends FunctionApplicationTerm(sl, receiver, function, arguments)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(receiver) ++ arguments
}

object PFunctionApplicationTerm {
  def unapply(t: PFunctionApplicationTerm): Option[(SourceLocation, PTerm, Function, PTermSequence)] =
    Some((t.sl, t.receiver, t.function, t.arguments))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with PTerm {
  override val arguments: PTermSequence = pArguments

  protected val pArguments: PTermSequence
}

object PDomainFunctionApplicationTerm {
  def unapply(t: PDomainFunctionApplicationTerm): Option[(SourceLocation, DomainFunction, PTermSequence)] =
    Some((t.sl, t.function, t.arguments))
}

private[silAST] final class PDomainFunctionApplicationTermC(
                                                             sl: SourceLocation,
                                                             override val function: DomainFunction,
                                                             override val arguments: PTermSequence
                                                             )
  extends DomainFunctionApplicationTerm(sl, function, arguments)
  with PDomainFunctionApplicationTerm
{
  override val pSubTerms = arguments
  override val pArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
private[silAST] final class PCastTerm(
                                        sl: SourceLocation,
                                        override val operand1: PTerm,
                                        override val newType: DataType
                                        )
  extends CastTerm(sl, operand1, newType)
  with PTerm {
  override val pSubTerms: Seq[PTerm] = List(operand1)
}

object PCastTerm {
  def unapply(t: PCastTerm): Option[(SourceLocation, PTerm, DataType)] =
    Some((t.sl, t.operand1, t.newType))
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFieldReadTerm private[silAST](
                                             sl: SourceLocation,
                                             override val location: PTerm,
                                             field: Field
                                             )
  extends FieldReadTerm(sl, location, field)
  with PTerm {
  override val pSubTerms: Seq[PTerm] = List(location)
}

object PFieldReadTerm {
  def unapply(t: PFieldReadTerm): Option[(SourceLocation, PTerm, Field)] =
    Some((t.sl, t.location, t.field))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class POldFieldReadTerm private[silAST](
                                                sl: SourceLocation,
                                                override val location: PTerm,
                                                field: Field
                                                )
  extends OldFieldReadTerm(sl, location, field)
  with PTerm {
  override val pSubTerms: Seq[PTerm] = List(location)
}

object POldFieldReadTerm {
  def unapply(t: POldFieldReadTerm): Option[(SourceLocation, PTerm, Field)] =
    Some((t.sl, t.location, t.field))
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DTerm extends Term {
  override val subTerms: Seq[DTerm] = dSubTerms
  protected val dSubTerms: Seq[DTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class BoundVariableTerm protected[silAST](
                                                       sl: SourceLocation,
                                                       variable: BoundVariable
                                                       )
  extends ASTNode(sl)
  with DTerm {
  override val toString = variable.name

  override val subNodes = List(variable)

  override val dSubTerms = Nil

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with DTerm {
  override val arguments: DTermSequence = dArguments
  protected val dArguments: DTermSequence
}

object DDomainFunctionApplicationTerm {
  def unapply(t: DDomainFunctionApplicationTerm): Option[(SourceLocation, DomainFunction, DTermSequence)] =
    Some((t.sl, t.function, t.arguments))
}


private[silAST] final class DDomainFunctionApplicationTermC(
                                                             sl: SourceLocation,
                                                             function: DomainFunction,
                                                             arguments: DTermSequence
                                                             )
  extends DomainFunctionApplicationTerm(sl, function, arguments)
  with DDomainFunctionApplicationTerm
{
  override val dSubTerms = arguments
  override val dArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains + Programs = General

sealed trait GTerm extends Term with DTerm with PTerm {
  override val subTerms: Seq[GTerm] = gSubTerms

  protected override val dSubTerms = gSubTerms
  protected override val pSubTerms = gSubTerms
  protected val gSubTerms: Seq[GTerm]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract case class LiteralTerm protected[silAST](sl: SourceLocation)
  extends ASTNode(sl) with Term
  with GTerm
  with AtomicTerm
  with AtomicNode {
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class IntegerLiteralTerm private[silAST](sl: SourceLocation, val value: BigInt)
  extends LiteralTerm(sl)
  with GTerm
  with AtomicNode {
  override val toString: String = value.toString()
  override val gSubTerms = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GDomainFunctionApplicationTerm(
                                            sl: SourceLocation,
                                            function: DomainFunction,
                                            override val arguments: GTermSequence
                                            )
  extends DomainFunctionApplicationTerm(sl, function, arguments)
  with DDomainFunctionApplicationTerm
  with PDomainFunctionApplicationTerm
  with GTerm {
  //  override val arguments : GTermSequence = gArguments
  override val dArguments = gArguments
  override val pArguments = gArguments
  protected val gArguments: GTermSequence = arguments
  protected val gSubTerms: Seq[GTerm] = arguments
}
