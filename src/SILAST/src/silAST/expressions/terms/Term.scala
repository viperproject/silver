package silAST.expressions.terms

import silAST.symbols.logical.quantification.LogicalVariable
import silAST.ASTNode
import silAST.expressions.util.{GTermSequence, DTermSequence, PTermSequence, TermSequence}
import silAST.programs.symbols.{Predicate, ProgramVariable, Field, Function}
import silAST.domains._
import silAST.types.{integerType, referenceType, permissionType, DataType}
import silAST.source.{TypeSubstitutedSourceLocation, SourceLocation}
import silAST.expressions.{PProgramVariableSubstitution, ProgramVariableSubstitution}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait Term extends ASTNode {
  def subTerms: Seq[Term]

  def dataType: DataType

  def freeVariables: collection.immutable.Set[LogicalVariable]

  def programVariables: collection.immutable.Set[ProgramVariable]

  def substitute(s: TypeVariableSubstitution): Term
  def substitute(s: LogicalVariableSubstitution): Term
  def substitute(s: ProgramVariableSubstitution): Term
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait AtomicTerm extends Term {
  final override lazy val subTerms : Seq[GTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Assertion terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class OldTerm private[silAST]
    (term: Term)
    (override val sourceLocation : SourceLocation)
  extends ASTNode
  with Term
{
  override val toString: String = "old(" + term.toString + ")"

  override val subTerms: Seq[Term] = List(term)

  override def dataType = term.dataType

  override def freeVariables = term.freeVariables

  override def programVariables = term.programVariables

  def substitute(s: TypeVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: LogicalVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: ProgramVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationTerm private[silAST]
    (private val f: DomainFunction, private val as: TermSequence )
    (override val sourceLocation : SourceLocation)
  extends ASTNode with Term
{
  require (f!=null)
  require(as != null)
  require(as.forall(_ != null))
  require(f.signature.parameterTypes.length == as.length)
  require(f.signature.parameterTypes.zip(as).forall((x) => x._2.dataType.isCompatible(x._1)),
    "type mismatch in domain function application: " +
      function.name +
      function.signature.parameterTypes.mkString("(", ",", ")") +
      " = " +
      (for (a <- as) yield a.toString + " : " + a.dataType.toString).mkString("(", ",", ")")

  )

  override lazy val toString: String = function.toString(as)

  override lazy val subTerms: Seq[Term] = arguments

  def function: DomainFunction = f

  def arguments: TermSequence = as

  override def dataType = function.signature.resultType

  override def freeVariables = arguments.freeVariables

  override def programVariables = arguments.programVariables

  def substitute(s: TypeVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: LogicalVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: ProgramVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FunctionApplicationTerm private[silAST]
    (receiver: Term, function: Function, arguments: TermSequence)
    (override val sourceLocation : SourceLocation)
  extends ASTNode with Term
{
  require(receiver.dataType == referenceType)
  require(function.signature.parameters.length == arguments.length)
  require(function.signature.parameters.zip(arguments).forall((x) => x._2.dataType.isCompatible(x._1.dataType)),
    "type mismatch in function application: " +
      function.name +
      (for (p <- function.signature.parameters) yield p.dataType).mkString("(", ",", ")") +
      " = " +
      (for (a <- arguments) yield a.toString + " : " + a.dataType.toString).mkString("(", ",", ")")
  )

  override val toString: String = receiver.toString + "." + function.name + arguments.toString

  override lazy val subTerms: Seq[Term] = List(receiver) ++ arguments.toList

  override def dataType = function.signature.result.dataType

  override def freeVariables = arguments.freeVariables ++ receiver.freeVariables

  override def programVariables = arguments.programVariables ++ receiver.programVariables

  def substitute(s: TypeVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation))
  def substitute(s: LogicalVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation))
  def substitute(s: ProgramVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingTerm private[silAST]
    (receiver: Term, predicate: Predicate, term: Term)
    (override val sourceLocation : SourceLocation)
  extends ASTNode with Term
{
  require(receiver.dataType == referenceType)

  override lazy val toString: String = "unfolding " + receiver.toString + "." + predicate.name + " in (" + term.toString + ")"

  override lazy val subTerms: Seq[Term] = List(receiver, term)

  override def dataType = term.dataType

  override def freeVariables = receiver.freeVariables ++ term.freeVariables

  override def programVariables = receiver.programVariables ++ term.programVariables

  def substitute(s: TypeVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(receiver.substitute(s), predicate, term.substitute(s))(
      s.sourceLocation(sourceLocation)
    )
  def substitute(s: LogicalVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(receiver.substitute(s), predicate, term.substitute(s))(
      s.sourceLocation(sourceLocation)
    )
  def substitute(s: ProgramVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(receiver.substitute(s), predicate, term.substitute(s))(
      s.sourceLocation(sourceLocation)
    )
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class CastTerm protected[silAST]
    (operand1: Term, newType: DataType)
    (override val sourceLocation : SourceLocation)
  extends ASTNode with Term
{
  override val toString: String = "(" + operand1 + ") : " + newType.toString

  override lazy val subTerms: Seq[Term] = operand1 :: Nil

  override def dataType = newType

  override def freeVariables = operand1.freeVariables

  override def programVariables = operand1.programVariables

  def substitute(s: TypeVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType.substitute(s))( s.sourceLocation(sourceLocation))
  def substitute(s: LogicalVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType)( s.sourceLocation(sourceLocation))
  def substitute(s: ProgramVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType)( s.sourceLocation(sourceLocation))
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldReadTerm protected[silAST]
    (location: Term,field: Field)
    (override val sourceLocation : SourceLocation)
  extends ASTNode with Term
{
  require(location.dataType == referenceType)

  override lazy val toString: String = location.toString + "." + field.name
  override lazy val subTerms: Seq[Term] = List(location)

  override lazy val dataType = field.dataType

  override def freeVariables = location.freeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
  def substitute(s: LogicalVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
  def substitute(s: ProgramVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PermTerm protected[silAST]
    (location: Term,field: Field)
    (override val sourceLocation : SourceLocation)
  extends ASTNode with Term
{
  require(location.dataType == referenceType)

  override lazy val toString: String = "perm(" + location.toString + "." + field.name + ")";
  override lazy val subTerms: Seq[Term] = List(location)

  override lazy val dataType = permissionType

  override def freeVariables = location.freeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
  def substitute(s: LogicalVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
  def substitute(s: ProgramVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FullPermissionTerm()
    (override val sourceLocation:SourceLocation)
  extends LiteralTerm
  with AtomicTerm
{
  override def toString: String = "write"

  override val gSubTerms = Seq[GTerm]()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution) : FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution) : FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution) : FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution) : FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class NoPermissionTerm()
    (override val sourceLocation:SourceLocation)
  extends LiteralTerm
  with AtomicTerm
{
  override def toString: String = "0"

  override val gSubTerms = Seq()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution) : NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution) : NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution) : NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution) : NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class EpsilonPermissionTerm()
    (override val sourceLocation:SourceLocation)
  extends LiteralTerm
  with AtomicTerm
{
  override def toString: String = "E"

  override val gSubTerms = Seq()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution) : EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution) : EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution) : EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution) : EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
sealed trait PTerm extends Term {
  override lazy val subTerms: Seq[PTerm] = pSubTerms

  protected def pSubTerms: Seq[PTerm]

  final override lazy val freeVariables = Set[LogicalVariable]()

  def substitute(s: TypeVariableSubstitution): PTerm

  def substitute(s: PLogicalVariableSubstitution): PTerm
  def substitute(s: PProgramVariableSubstitution): PTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableTerm protected[silAST]
    (variable: ProgramVariable)
    (override val sourceLocation : SourceLocation)
  extends ASTNode
  with PTerm
  with AtomicTerm
{
  override val toString: String = variable.name
  override val pSubTerms = Nil

  override def dataType = variable.dataType

  override def programVariables = Set(variable)

  def substitute(s: TypeVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation))

  def substitute(s: LogicalVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation))
  def substitute(s: PLogicalVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation))

  //Must have mapping
  def substitute(s: ProgramVariableSubstitution): Term = s.mapVariable(variable).get
  def substitute(s: PProgramVariableSubstitution): PTerm = s.mapVariable(variable).get
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnfoldingTerm private[silAST]
    (receiver: PTerm,predicate: Predicate,term: PTerm)
    (sourceLocation : SourceLocation)
  extends UnfoldingTerm(receiver, predicate, term)(sourceLocation) with PTerm
{
  require(receiver.dataType == referenceType)

  override val pSubTerms: Seq[PTerm] = List(receiver, term)
  //  override def substitute(s: LogicalVariableSubstitution): UnfoldingTerm = new UnfoldingTerm(sourceLocation,receiver.substitute(s),predicate,term.substitute(s))
  override def substitute(s: TypeVariableSubstitution): PUnfoldingTerm =
    new PUnfoldingTerm(receiver.substitute(s), predicate, term.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: PLogicalVariableSubstitution): PUnfoldingTerm =
    new PUnfoldingTerm(receiver.substitute(s), predicate, term.substitute(s))(s.sourceLocation(sourceLocation))

  override def substitute(s: PProgramVariableSubstitution): PUnfoldingTerm =
    new PUnfoldingTerm(receiver.substitute(s), predicate, term.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFunctionApplicationTerm private[silAST]
    (override val receiver: PTerm,function: Function, override val arguments: PTermSequence)
    (sourceLocation : SourceLocation)
  extends FunctionApplicationTerm(receiver, function, arguments)(sourceLocation)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(receiver) ++ arguments

  override def substitute(s: TypeVariableSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(s.sourceLocation(sourceLocation))

  def substitute(s: PLogicalVariableSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(s.sourceLocation(sourceLocation))

  def substitute(s: PProgramVariableSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}

object PFunctionApplicationTerm {
  def unapply(t: PFunctionApplicationTerm): Option[(PTerm, Function, PTermSequence)] =
    Some((t.receiver, t.function, t.arguments))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with PTerm
{
  override val arguments: PTermSequence = pArguments

  protected def pArguments: PTermSequence

  override def substitute(s: TypeVariableSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation))

  def substitute(s: PLogicalVariableSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(function, arguments.substitute(s))(s.sourceLocation(sourceLocation))

  def substitute(s: PProgramVariableSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(function, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}

object PDomainFunctionApplicationTerm {
  def unapply(t: PDomainFunctionApplicationTerm): Option[(DomainFunction, PTermSequence)] =
    Some((t.function, t.arguments))
}

private[silAST] final class PDomainFunctionApplicationTermC
    (function: DomainFunction,arguments: PTermSequence)
    (sourceLocation : SourceLocation)
  extends DomainFunctionApplicationTerm(function, arguments)(sourceLocation)
  with PDomainFunctionApplicationTerm
{
  override val pSubTerms = arguments
  override val pArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PCastTerm private[silAST]
    (override val operand1: PTerm,override val newType: DataType)
    (sourceLocation : SourceLocation)
  extends CastTerm(operand1, newType)(sourceLocation)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(operand1)

  override def substitute(s: TypeVariableSubstitution): PCastTerm =
    new PCastTerm(operand1.substitute(s), newType.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: PLogicalVariableSubstitution): PCastTerm =
    new PCastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation))
  def substitute(s: PProgramVariableSubstitution): PCastTerm =
    new PCastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation))
}

object PCastTerm {
  def unapply(t: PCastTerm): Option[(PTerm, DataType)] =
    Some((t.operand1, t.newType))
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFieldReadTerm private[silAST]
    (override val location: PTerm,field: Field)
    (sourceLocation : SourceLocation)
  extends FieldReadTerm(location, field)(sourceLocation)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(location)

  override def substitute(s: TypeVariableSubstitution): PFieldReadTerm =
    new PFieldReadTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
  def substitute(s: PLogicalVariableSubstitution): PFieldReadTerm =
    new PFieldReadTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
  def substitute(s: PProgramVariableSubstitution): PFieldReadTerm =
    new PFieldReadTerm(location.substitute(s), field)(s.sourceLocation(sourceLocation))
}

object PFieldReadTerm {
  def unapply(t: PFieldReadTerm): Option[(PTerm, Field)] =
    Some((t.location, t.field))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DTerm extends Term {
  protected def dSubTerms: Seq[DTerm]

  override lazy val subTerms: Seq[DTerm] = dSubTerms

  final override def programVariables = Set()

  override def substitute(s: TypeVariableSubstitution): DTerm
  def substitute(s: DLogicalVariableSubstitution): DTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class LogicalVariableTerm protected[silAST]
    (variable: LogicalVariable)
    (override val sourceLocation : SourceLocation)
  extends ASTNode
  with DTerm
{
  override val toString = variable.name
  override val dSubTerms = Nil

  override def dataType = variable.dataType

  override def freeVariables = Set(variable)

  def substitute(s: TypeVariableSubstitution): LogicalVariableTerm =
    s.mapVariable(variable) match {
      case Some(t: LogicalVariable) => new LogicalVariableTerm(t)(s.sourceLocation(sourceLocation))
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation))
    }

  def substitute(s: LogicalVariableSubstitution): Term =
    s.mapVariable(variable) match {
      case Some(t: DTerm) => t
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation))
    }

  def substitute(s: DLogicalVariableSubstitution): DTerm =
    s.mapVariable(variable) match {
      case Some(t: DTerm) => t
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation))
    }

  def substitute(s: ProgramVariableSubstitution): Term =
    this

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainFunctionApplicationTerm
  extends DomainFunctionApplicationTerm
  with DTerm
{
  protected def dArguments: DTermSequence

  override def arguments: DTermSequence = dArguments

  override def substitute(s: TypeVariableSubstitution): DDomainFunctionApplicationTerm =
    new DDomainFunctionApplicationTermC(function.substitute(s), arguments.substitute(s))(s.sourceLocation((sourceLocation)))

  def substitute(s: DLogicalVariableSubstitution): DDomainFunctionApplicationTerm =
    new DDomainFunctionApplicationTermC(function, arguments.substitute(s))(s.sourceLocation((sourceLocation)))
}

object DDomainFunctionApplicationTerm {
  def unapply(t: DDomainFunctionApplicationTerm): Option[(DomainFunction, DTermSequence)] =
    Some((t.function, t.arguments))
}


private[silAST] final class DDomainFunctionApplicationTermC
    (function: DomainFunction,arguments: DTermSequence)
    (sourceLocation : SourceLocation)
  extends DomainFunctionApplicationTerm(function, arguments)(sourceLocation)
  with DDomainFunctionApplicationTerm
{
  override val dSubTerms = arguments
  override val dArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains + Programs = General

sealed trait GTerm extends Term with DTerm with PTerm {
  override lazy val subTerms: Seq[GTerm] = gSubTerms

  protected def gSubTerms: Seq[GTerm]

  protected override val dSubTerms = gSubTerms
  protected override val pSubTerms = gSubTerms

  def substitute(s: TypeVariableSubstitution): GTerm
  def substitute(s: GLogicalVariableSubstitution): GTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract case class LiteralTerm protected[silAST]()
  extends ASTNode with Term
  with GTerm
  with AtomicTerm
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class IntegerLiteralTerm private[silAST]
    (val value: BigInt)
    (override val sourceLocation : SourceLocation)
  extends LiteralTerm
  with GTerm
{
  override val toString: String = value.toString()
  override val gSubTerms = Nil

  override def dataType = integerType

  override def substitute(s: TypeVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation))

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GDomainFunctionApplicationTerm
    (function: DomainFunction,override val arguments: GTermSequence)
    (sourceLocation : SourceLocation)
  extends DomainFunctionApplicationTerm(function, arguments)(sourceLocation)
  with DDomainFunctionApplicationTerm
  with PDomainFunctionApplicationTerm
  with GTerm
{
  //  override val parameters : GTermSequence = gArguments
  override val dArguments = gArguments
  override val pArguments = gArguments
  protected val gArguments: GTermSequence = arguments
  protected val gSubTerms: Seq[GTerm] = gArguments

  override val dataType = function.signature.resultType

  override def substitute(s: TypeVariableSubstitution): GDomainFunctionApplicationTerm =
    new GDomainFunctionApplicationTerm(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation))
  def substitute(s: GLogicalVariableSubstitution): GDomainFunctionApplicationTerm =
    new GDomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}
