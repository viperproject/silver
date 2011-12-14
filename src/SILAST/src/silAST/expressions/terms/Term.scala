package silAST.expressions.terms

import silAST.symbols.logical.quantification.BoundVariable
import silAST.ASTNode
import silAST.expressions.util.{GTermSequence, DTermSequence, PTermSequence, TermSequence}
import silAST.programs.symbols.{Predicate, ProgramVariable, Field, Function}
import silAST.domains._
import silAST.types.{permissionType, DataType}
import silAST.source.{noLocation, SourceLocation}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait Term extends ASTNode {
  def subTerms: Seq[Term]
  def dataType : DataType
  def freeVariables : collection.immutable.Set[BoundVariable]
  def programVariables : collection.immutable.Set[ProgramVariable]

  def substitute(s: Substitution): Term
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

  override val subTerms: Seq[Term] = List(term)

  override def dataType         = term.dataType
  override def freeVariables    = term.freeVariables
  override def programVariables = term.programVariables //TODO:old versions
  def substitute(s: Substitution): OldTerm = new OldTerm(sl,term.substitute(s))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationTerm private[silAST](
                                                                 sl: SourceLocation,
                                                                 private val f: DomainFunction,
                                                                 private val a: TermSequence
                                                                 ) extends ASTNode(sl) with Term {
  override val toString: String = function.toString(arguments)
  override val subTerms: Seq[Term] = arguments

  def function : DomainFunction = f
  def arguments : TermSequence = a

  override def dataType         = function.signature.resultType
  override def freeVariables    = arguments.freeVariables
  override def programVariables = arguments.programVariables
  def substitute(s: Substitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(sl,function.substitute(s),arguments.substitute(s))
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

  override val subTerms: Seq[Term] = List(receiver) ++ arguments.toList

  override def dataType         = function.signature.result.dataType
  override def freeVariables    = arguments.freeVariables ++ receiver.freeVariables
  override def programVariables = arguments.programVariables ++ receiver.programVariables

  def substitute(s: Substitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(sl,receiver.substitute(s),function,arguments.substitute(s))
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

  override val subTerms: Seq[Term] = List(receiver,term)

  override def dataType         = term.dataType
  override def freeVariables    = receiver.freeVariables ++ term.freeVariables
  override def programVariables = receiver.programVariables ++ term.programVariables
  def substitute(s: Substitution): UnfoldingTerm =
    new UnfoldingTerm(sl,receiver.substitute(s),predicate,term.substitute(s))
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

  override val subTerms: Seq[Term] = operand1 :: Nil

  override def dataType         = newType
  override def freeVariables    = operand1.freeVariables
  override def programVariables = operand1.programVariables
  def substitute(s: Substitution): CastTerm =
    new CastTerm(sl,operand1.substitute(s),newType.substitute(s))
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
  override val subTerms: Seq[Term] = List(location)

  override def dataType         = field.dataType
  override def freeVariables    = location.freeVariables
  override def programVariables = location.programVariables
  def substitute(s: Substitution): FieldReadTerm =
    new FieldReadTerm(sl,location.substitute(s),field)
}
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
object fullPermissionTerm extends LiteralTerm(noLocation) with AtomicTerm
{
  override def toString: String = "write"
  override val gSubTerms = Seq[GTerm]()
  override val dataType = permissionType
  override def substitute(s: Substitution): LiteralTerm = this
  override def substitute(s: DSubstitution): LiteralTerm = this
  override def substitute(s: PSubstitution): LiteralTerm = this
  override def substitute(s: GSubstitution): LiteralTerm = this
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
object noPermissionTerm extends LiteralTerm(noLocation) with AtomicTerm
{
  override def toString: String = "0"
  override val gSubTerms = Seq()
  override val dataType = permissionType
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
object epsilonPermissionTerm extends LiteralTerm(noLocation) with AtomicTerm
{
  override def toString: String = "E"
  override val gSubTerms = Seq()
  override val dataType = permissionType
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

  protected def pSubTerms: Seq[PTerm]
  
  final override val freeVariables = Set[BoundVariable]()

  def substitute(s: PSubstitution): PTerm
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
  override val pSubTerms = Nil

  override def dataType         = variable.dataType
  override def programVariables = Set(variable)

  def substitute(s: Substitution): ProgramVariableTerm = this
  def substitute(s: PSubstitution): ProgramVariableTerm = this
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
  override val pSubTerms: Seq[PTerm] = List(receiver,term)
//  override def substitute(s: Substitution): UnfoldingTerm = new UnfoldingTerm(sl,receiver.substitute(s),predicate,term.substitute(s))
  def substitute(s: PSubstitution): PUnfoldingTerm = new PUnfoldingTerm(sl,receiver.substitute(s),predicate,term.substitute(s))
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
//  def substitute(s: Substitution): FunctionApplicationTerm =
//    new FunctionApplicationTerm(sl,receiver.substitute(s),function,arguments.substitute(s))
  def substitute(s: PSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(sl,receiver.substitute(s),function,arguments.substitute(s))
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
//  def substitute(s: Substitution): DomainFunctionApplicationTerm =
//    new DomainFunctionApplicationTerm(sl,function,arguments.substitute(s))
  def substitute(s: PSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(sl,function,arguments.substitute(s))
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
final class PCastTerm private[silAST] (
                                       sl: SourceLocation,
                                       override val operand1: PTerm,
                                       override val newType: DataType
                                       )
  extends CastTerm(sl, operand1, newType)
  with PTerm {
  override val pSubTerms: Seq[PTerm] = List(operand1)

  def substitute(s: PSubstitution): PCastTerm =
    new PCastTerm(sl,operand1.substitute(s),newType.substitute(s))
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

  def substitute(s: PSubstitution): PFieldReadTerm =
    new PFieldReadTerm(sl,location.substitute(s),field)
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
  protected def dSubTerms: Seq[DTerm]
  override val subTerms: Seq[DTerm] = dSubTerms

  final override def programVariables = Set()
  def substitute(s: DSubstitution): DTerm
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
  override val dSubTerms = Nil

  override def dataType      = variable.dataType
  override def freeVariables = Set(variable)

  def substitute(s: Substitution): Term =
    s.mapVariable(variable) match {case Some(t:DTerm) => t case _ => this}
  def substitute(s: DSubstitution): DTerm =
    s.mapVariable(variable) match {case Some(t:DTerm) => t case _ => this}
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with DTerm
{
  protected def dArguments: DTermSequence
  override def arguments: DTermSequence = dArguments

  def substitute(s: DSubstitution): DDomainFunctionApplicationTerm =
    new DDomainFunctionApplicationTermC(sl,function.substitute(s),arguments.substitute(s))
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

  protected def gSubTerms: Seq[GTerm]
  protected override val dSubTerms = gSubTerms
  protected override val pSubTerms = gSubTerms
  def substitute(s: GSubstitution): GTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract case class LiteralTerm protected[silAST](sl: SourceLocation)
  extends ASTNode(sl) with Term
  with GTerm
  with AtomicTerm
{
  def substitute(s: Substitution): LiteralTerm = this
  def substitute(s: DSubstitution): LiteralTerm = this
  def substitute(s: PSubstitution): LiteralTerm = this
  def substitute(s: GSubstitution): LiteralTerm = this
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class IntegerLiteralTerm private[silAST](sl: SourceLocation, val value: BigInt)
  extends LiteralTerm(sl)
  with GTerm
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
  protected val gSubTerms: Seq[GTerm] = gArguments

  override val dataType      = function.signature.resultType

  def substitute(s: GSubstitution): GDomainFunctionApplicationTerm =
    new GDomainFunctionApplicationTerm(sl,function.substitute(s),arguments.substitute(s))
}



