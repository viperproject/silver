package silAST.expressions.terms

import silAST.symbols.logical.quantification.BoundVariable
import silAST.types.DataType
import silAST.{AtomicNode, ASTNode}
import silAST.domains.DomainFunction
import silAST.expressions.util.{GTermSequence, DTermSequence, PTermSequence, TermSequence}
import silAST.programs.symbols.{Predicate, ProgramVariable, Field, Function}
import silAST.source.{noLocation, SourceLocation}
import silAST.expressions.PredicateExpression

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait Term extends ASTNode {
  def subTerms: Seq[Term]
  def dataType : DataType
  def freeVariables : collection.immutable.Set[BoundVariable]
  def programVariables : collection.immutable.Set[ProgramVariable]
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
sealed case class OldTerm private[silAST](
                                                                 sl: SourceLocation,
                                                                 term : Term
                                                                 ) extends ASTNode(sl) with Term {
  override val toString: String = "old(" + term.toString + ")"

  override val subNodes: Seq[ASTNode] = List(term)

  override val subTerms: Seq[Term] = List(term)

  override def dataType         = term.dataType
  override def freeVariables    = term.freeVariables
  override def programVariables = term.programVariables //TODO:old versions
}

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

  override def dataType         = function.signature.resultType
  override def freeVariables    = arguments.freeVariables
  override def programVariables = arguments.programVariables
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

  override def dataType         = function.signature.result.dataType
  override def freeVariables    = arguments.freeVariables ++ receiver.freeVariables
  override def programVariables = arguments.programVariables ++ receiver.programVariables

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingTerm private[silAST](
                                                           sl: SourceLocation,
                                                           receiver : Term,
                                                           predicate : Predicate,
                                                           term : Term
                                                           ) extends ASTNode(sl) with Term {
  override val toString: String = "unfolding " + receiver.toString + "." + predicate.name + " in (" + term.toString + ")"

  override val subNodes: Seq[ASTNode] = List(receiver,predicate,term)

  override val subTerms: Seq[Term] = List(receiver,term)

  override def dataType         = term.dataType
  override def freeVariables    = receiver.freeVariables ++ term.freeVariables
  override def programVariables = receiver.programVariables ++ term.programVariables
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

  override def dataType         = newType
  override def freeVariables    = operand1.freeVariables
  override def programVariables = operand1.programVariables
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
  override val subNodes: Seq[ASTNode] = List(location,field)
  override val subTerms: Seq[Term] = List(location)

  override def dataType         = field.dataType
  override def freeVariables    = location.freeVariables
  override def programVariables = location.programVariables
}

/*
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PermissionTerm protected[silAST](sl: SourceLocation)
  extends ASTNode(sl)
{
  override def toString: String
}

final case class FullPermissionTerm private()
  extends PermissionTerm(noLocation) with AtomicNode {
  override def toString: String = "write"
}

private[silAST] object FullPermissionTerm {
  val fullPermissionTerm = new FullPermissionTerm()
}

final case class NoPermissionTerm private()
  extends PermissionTerm(noLocation) with AtomicNode {
  override def toString: String = "none"
}

private[silAST] object NoPermissionTerm {
  val noPermissionTerm = new NoPermissionTerm()
}

final case class PercentagePermissionTerm private[silAST](sl: SourceLocation, percentage: Int)
  extends PermissionTerm(sl) with AtomicNode {
  require(percentage > 0)
  require(percentage < 100)

  override def toString: String = percentage.toString + "%"
}

final case class EpsilonPermissionTerm private()
  extends PermissionTerm(noLocation) with AtomicNode {
  override def toString: String = "epsilon"
}

private[silAST] object EpsilonPermissionTerm {
  val epsilonPermissionTerm = new EpsilonPermissionTerm()
}

final case class PermissionVariableTerm private[silAST](
                                                         sl: SourceLocation,
                                                         variable: PermissionVariable
                                                         )
  extends PermissionTerm(sl) with AtomicNode {
  override def toString: String = variable.name

}


final case class PermissionAdditionTerm private[silAST](
                                                         sl: SourceLocation,
                                                         t1: PermissionTerm,
                                                         t2: PermissionTerm
                                                         ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "+" + t2.toString

  override val subNodes = List(t1, t2)
}

final case class PermissionSubtractionTerm private[silAST](
                                                            sl: SourceLocation,
                                                            t1: PermissionTerm,
                                                            t2: PermissionTerm
                                                            ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "-" + t2.toString

  override val subNodes = List(t1, t2)
}

final case class PermissionMultiplicationTerm private[silAST](
                                                               sl: SourceLocation,
                                                               t1: PermissionTerm,
                                                               t2: PermissionTerm
                                                               ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "*" + t2.toString

  override val subNodes = List(t1, t2)
}

final case class PermissionIntegerMultiplicationTerm private[silAST](
                                                                      sl: SourceLocation,
                                                                      t1: PermissionTerm,
                                                                      t2: Int
                                                                      ) extends PermissionTerm(sl) {
  override def toString: String = t1.toString + "+" + t2.toString

  override val subNodes = List(t1)
}
*/

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
sealed trait PTerm extends Term {
  override val subTerms: Seq[PTerm] = pSubTerms

  protected def pSubTerms: Seq[PTerm]
  
  final override val freeVariables = Set[BoundVariable]()
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableTerm protected[silAST](
                                                         sl: SourceLocation,
                                                         variable: ProgramVariable
                                                         )
  extends ASTNode(sl)
  with PTerm
  with AtomicTerm
{

  override val toString: String = variable.name
  override val subNodes: Seq[ASTNode] = List(variable)
  override val pSubTerms = Nil

  override def dataType         = variable.dataType
  override def programVariables = Set(variable)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnfoldingTerm private[silAST](
                                                 sl: SourceLocation,
                                                 receiver: PTerm,
                                                 predicate : Predicate,
                                                 term : PTerm
                                                 ) extends UnfoldingTerm(sl,receiver,predicate,term) with PTerm
{
  override val subNodes: Seq[ASTNode] = List(receiver, predicate,term)
  override val pSubTerms: Seq[PTerm] = List(receiver,term)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFunctionApplicationTerm private[silAST](
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

  protected def pArguments: PTermSequence
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
  with PDomainFunctionApplicationTerm {
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
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DTerm extends Term {
  override val subTerms: Seq[DTerm] = dSubTerms
  protected val dSubTerms: Seq[DTerm]

  final override def programVariables = Set()
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class BoundVariableTerm protected[silAST](
                                                       sl: SourceLocation,
                                                       variable: BoundVariable
                                                       )
  extends ASTNode(sl)
  with DTerm
{
  override val toString = variable.name
  override val subNodes = List(variable)
  override val dSubTerms = Nil

  override def dataType      = variable.dataType
  override def freeVariables = Set(variable)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with DTerm
{
  protected val dArguments: DTermSequence
  override val arguments: DTermSequence = dArguments

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
  with DDomainFunctionApplicationTerm {
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
  with AtomicNode
{
  override val toString: String = value.toString()
  override val gSubTerms = Nil

  override def dataType      = null//TODO integerType
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
  //  override val parameters : GTermSequence = gArguments
  override val dArguments = gArguments
  override val pArguments = gArguments
  protected val gArguments: GTermSequence = arguments
  protected val gSubTerms: Seq[GTerm] = arguments

  override val dataType      = function.signature.resultType
}
