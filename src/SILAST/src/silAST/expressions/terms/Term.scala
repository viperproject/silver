package silAST.expressions.terms

import silAST.symbols.logical.quantification.LogicalVariable
import silAST.ASTNode
import silAST.expressions.util.{GTermSequence, DTermSequence, PTermSequence, TermSequence}
import silAST.programs.symbols.{Predicate, ProgramVariable, Field, Function}
import silAST.domains._
import silAST.source.SourceLocation
import silAST.types._
import silAST.expressions.{PPredicatePermissionExpression, PredicatePermissionExpression, PProgramVariableSubstitution, ProgramVariableSubstitution}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Location
  extends ASTNode
{
  override val sourceLocation = receiver.sourceLocation
  override val comment = Nil
  def receiver: Term
  def dataType : DataType

  require(receiver.dataType == referenceType)

  def freeVariables: collection.immutable.Set[LogicalVariable]

  def programVariables: collection.immutable.Set[ProgramVariable]

  def substitute(s: TypeVariableSubstitution): Location
  def substitute(s: LogicalVariableSubstitution): Location
  def substitute(s: ProgramVariableSubstitution): Location
}

sealed trait PLocation extends Location
{
  override def receiver : PTerm
  def substitute(s: TypeVariableSubstitution): PLocation
  def substitute(s: PLogicalVariableSubstitution): PLocation
  def substitute(s: PProgramVariableSubstitution): PLocation
}

sealed case class FieldLocation private[silAST](receiver: Term,field : Field)  extends Location
{
  override val toString = receiver.toString + "." + field.name
  override lazy val dataType = field.dataType

  override def freeVariables = receiver.freeVariables

  override def programVariables = receiver.programVariables

  def substitute(s: TypeVariableSubstitution): FieldLocation =
    new FieldLocation(receiver.substitute(s),field)

  def substitute(s: LogicalVariableSubstitution): FieldLocation =
    new FieldLocation(receiver.substitute(s),field)

  def substitute(s: ProgramVariableSubstitution): FieldLocation =
    new FieldLocation(receiver.substitute(s),field)
}

final class PFieldLocation private[silAST](override val receiver: PTerm,field : Field)
  extends FieldLocation(receiver,field)
  with PLocation
{
  override def substitute(s: TypeVariableSubstitution): PFieldLocation =
    new PFieldLocation(receiver.substitute(s),field)

  def substitute(s: PLogicalVariableSubstitution): PFieldLocation =
    new PFieldLocation(receiver.substitute(s),field)

  def substitute(s: PProgramVariableSubstitution): PFieldLocation =
    new PFieldLocation(receiver.substitute(s),field)
}

sealed case class PredicateLocation private[silAST](receiver: Term,predicate : Predicate)
  extends Location
{
  override val toString = receiver.toString + "." + predicate.name
  override lazy val dataType = booleanType

  override def freeVariables = receiver.freeVariables

  override def programVariables = receiver.programVariables

  def substitute(s: TypeVariableSubstitution): PredicateLocation =
    new PredicateLocation(receiver.substitute(s),predicate)

  def substitute(s: LogicalVariableSubstitution): PredicateLocation =
    new PredicateLocation(receiver.substitute(s),predicate)

  def substitute(s: ProgramVariableSubstitution): PredicateLocation =
    new PredicateLocation(receiver.substitute(s),predicate)
}

final class PPredicateLocation private[silAST](override val receiver: PTerm,predicate : Predicate)
  extends PredicateLocation(receiver,predicate)
  with PLocation
{
  override def substitute(s: TypeVariableSubstitution): PPredicateLocation =
    new PPredicateLocation(receiver.substitute(s),predicate)

  override def substitute(s: PLogicalVariableSubstitution): PPredicateLocation =
    new PPredicateLocation(receiver.substitute(s),predicate)

  override def substitute(s: PProgramVariableSubstitution): PPredicateLocation =
    new PPredicateLocation(receiver.substitute(s),predicate)
}

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
  final override lazy val subTerms: Seq[GTerm] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Assertion terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class IfThenElseTerm private[silAST]
(condition: Term, pTerm: Term, nTerm: Term)
(override val sourceLocation: SourceLocation, override val comment : List[String])
  extends Term
{
  require(condition.dataType == booleanType)
  require(pTerm.dataType.isCompatible(nTerm.dataType))
  require(nTerm.dataType.isCompatible(pTerm.dataType))

  override val dataType = pTerm.dataType
  override val freeVariables = condition.freeVariables ++ pTerm.freeVariables ++ nTerm.freeVariables
  override val programVariables = condition.programVariables ++ pTerm.programVariables ++ nTerm.programVariables
  override lazy val subTerms: Seq[Term] = List(condition, pTerm, nTerm)

  def substitute(s: TypeVariableSubstitution): IfThenElseTerm =
    new IfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): IfThenElseTerm =
    new IfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): IfThenElseTerm =
    new IfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

sealed case class OldTerm private[silAST]
    (term: Term)
    (override val sourceLocation: SourceLocation, override val comment : List[String])
  extends ASTNode
  with Term
{
  override val toString: String = "old(" + term.toString + ")"

  override val subTerms: Seq[Term] = List(term)

  override def dataType = term.dataType

  override def freeVariables = term.freeVariables

  override def programVariables = term.programVariables

  def substitute(s: TypeVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationTerm private[silAST]
    (private val f: DomainFunction, private val as: TermSequence)
    (override val sourceLocation: SourceLocation, override val comment : List[String])
  extends ASTNode with Term
{
  require(f != null)
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
    new DomainFunctionApplicationTerm(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FunctionApplicationTerm private[silAST]
    (receiver: Term, function: Function, arguments: TermSequence)
    (override val sourceLocation: SourceLocation, override val comment : List[String])
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
      s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingTerm private[silAST]
(predicate : PredicatePermissionExpression, term: Term)
(override val sourceLocation: SourceLocation, val factory: PTermFactory, override val comment : List[String])
  extends ASTNode with Term
{
  override lazy val toString: String = "unfolding " + predicate.toString + " in (" + term.toString + ")"

  override lazy val subTerms: Seq[Term] = List(predicate.location.receiver,term)

  override def dataType = term.dataType

  override def freeVariables = predicate.freeVariables ++ term.freeVariables

  override def programVariables = predicate.programVariables ++ term.programVariables

  def substitute(s: TypeVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )

  def substitute(s: LogicalVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )

  def substitute(s: ProgramVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class CastTerm protected[silAST]
(operand1: Term, newType: DataType)
(override val sourceLocation: SourceLocation, override val comment : List[String])
  extends ASTNode with Term
{
  override val toString: String = "(" + operand1 + ") : " + newType.toString

  override lazy val subTerms: Seq[Term] = operand1 :: Nil

  override def dataType = newType

  override def freeVariables = operand1.freeVariables

  override def programVariables = operand1.programVariables

  def substitute(s: TypeVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation),Nil)
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldReadTerm protected[silAST]
(location : FieldLocation)
(override val sourceLocation: SourceLocation, override val comment : List[String])
  extends ASTNode with Term
{
  override lazy val toString: String = location.toString
  override lazy val subTerms: Seq[Term] = List(location.receiver)

  override lazy val dataType = location.dataType

  override def freeVariables = location.freeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PermTerm protected[silAST]
    (location: Location)
    (override val sourceLocation: SourceLocation, override val comment : List[String])
  extends ASTNode with Term
{
  override lazy val toString: String = "perm(" + location.toString + ")";
  override lazy val subTerms: Seq[Term] = List(location.receiver)

  override lazy val dataType = permissionType

  override def freeVariables = location.freeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: ProgramVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FullPermissionTerm()
    (sourceLocation: SourceLocation, comment : List[String])
  extends LiteralTerm()(sourceLocation,comment)
  with AtomicTerm
{
  override def toString: String = "write"

  override val gSubTerms = Seq[GTerm]()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: LogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: DLogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PLogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: GLogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: ProgramVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PProgramVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class NoPermissionTerm()
                           (sourceLocation: SourceLocation, comment : List[String])
  extends LiteralTerm()(sourceLocation,comment)
  with AtomicTerm
{
  override def toString: String = "0"

  override val gSubTerms = Seq()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: LogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: DLogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PLogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: GLogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: ProgramVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PProgramVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class EpsilonPermissionTerm()
                                (sourceLocation: SourceLocation, comment : List[String])
extends LiteralTerm()(sourceLocation,comment)
  with AtomicTerm
{
  override def toString: String = "E"

  override val gSubTerms = Seq()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: LogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: DLogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PLogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: GLogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: ProgramVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PProgramVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program terms
///////////////////////////////////////////////////////////////////////////
sealed trait PTerm extends Term
{
  override lazy val subTerms: Seq[PTerm] = pSubTerms

  protected def pSubTerms: Seq[PTerm]

  final override val freeVariables = Set[LogicalVariable]()

  def substitute(s: TypeVariableSubstitution): PTerm

  def substitute(s: PLogicalVariableSubstitution): PTerm

  def substitute(s: PProgramVariableSubstitution): PTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PIfThenElseTerm
  extends IfThenElseTerm
  with PTerm
{
  override val condition: PTerm = pCondition
  override val pTerm: PTerm = ppTerm
  override val nTerm: PTerm = pnTerm

  protected[silAST] def pCondition: PTerm

  protected[silAST] def ppTerm: PTerm

  protected[silAST] def pnTerm: PTerm

  override def substitute(s: TypeVariableSubstitution): PIfThenElseTerm =
    new PIfThenElseTermC(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PLogicalVariableSubstitution): PIfThenElseTerm =
    new PIfThenElseTermC(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PProgramVariableSubstitution): PIfThenElseTerm =
    new PIfThenElseTermC(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

object PIfThenElseTerm {
  def unapply(t: PIfThenElseTerm): Option[(PTerm, PTerm, PTerm)] =
    Some((t.condition, t.ppTerm, t.pnTerm))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
private[silAST] final class PIfThenElseTermC
(override val pCondition: PTerm, override val ppTerm: PTerm, override val pnTerm: PTerm)
(override val sourceLocation: SourceLocation, comment : List[String])
  extends IfThenElseTerm(pCondition, ppTerm, pnTerm)(sourceLocation,comment)
  with PIfThenElseTerm
{
  require(condition.dataType == booleanType)
  require(pTerm.dataType.isCompatible(nTerm.dataType))
  require(nTerm.dataType.isCompatible(pTerm.dataType))

  override val pSubTerms = List(condition, pTerm, nTerm)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableTerm protected[silAST]
(variable: ProgramVariable)
(override val sourceLocation: SourceLocation, override val comment : List[String])
  extends ASTNode
  with PTerm
  with AtomicTerm
{
  override val toString: String = variable.name
  override val pSubTerms = Nil

  override def dataType = variable.dataType

  override def programVariables = Set(variable)

  def substitute(s: TypeVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: LogicalVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PLogicalVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation),Nil)

  //Must have mapping
  def substitute(s: ProgramVariableSubstitution): Term = s.mapVariable(variable).get

  def substitute(s: PProgramVariableSubstitution): PTerm = s.mapVariable(variable).get
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFunctionApplicationTerm private[silAST]
(override val receiver: PTerm, function: Function, override val arguments: PTermSequence)
(sourceLocation: SourceLocation, comment : List[String])
  extends FunctionApplicationTerm(receiver, function, arguments)(sourceLocation,comment)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(receiver) ++ arguments

  override def substitute(s: TypeVariableSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PLogicalVariableSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PProgramVariableSubstitution): PFunctionApplicationTerm =
    new PFunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)
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
  override def arguments: PTermSequence = pArguments // needs to be a `def`, otherwise it is initialized to `null`.

  protected def pArguments: PTermSequence

  override def substitute(s: TypeVariableSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PLogicalVariableSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PProgramVariableSubstitution): PDomainFunctionApplicationTerm =
    new PDomainFunctionApplicationTermC(function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

object PDomainFunctionApplicationTerm {
  def unapply(t: PDomainFunctionApplicationTerm): Option[(DomainFunction, PTermSequence)] =
    Some((t.function, t.arguments))
}

private[silAST] final class PDomainFunctionApplicationTermC
(function: DomainFunction, arguments: PTermSequence)
(sourceLocation: SourceLocation, comment : List[String])
  extends DomainFunctionApplicationTerm(function, arguments)(sourceLocation,comment)
  with PDomainFunctionApplicationTerm
{
  override val pSubTerms = arguments
  override val pArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PCastTerm private[silAST]
(override val operand1: PTerm, override val newType: DataType)
(sourceLocation: SourceLocation, comment : List[String])
  extends CastTerm(operand1, newType)(sourceLocation,comment)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(operand1)

  override def substitute(s: TypeVariableSubstitution): PCastTerm =
    new PCastTerm(operand1.substitute(s), newType.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PLogicalVariableSubstitution): PCastTerm =
    new PCastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PProgramVariableSubstitution): PCastTerm =
    new PCastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation),Nil)
}

object PCastTerm {
  def unapply(t: PCastTerm): Option[(PTerm, DataType)] =
    Some((t.operand1, t.newType))
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PFieldReadTerm private[silAST]
(override val location: PFieldLocation)
(sourceLocation: SourceLocation, comment : List[String])
  extends FieldReadTerm(location)(sourceLocation,comment)
  with PTerm
{
  override val pSubTerms: Seq[PTerm] = List(location.receiver)

  override def substitute(s: TypeVariableSubstitution): PFieldReadTerm =
    new PFieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PLogicalVariableSubstitution): PFieldReadTerm =
    new PFieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: PProgramVariableSubstitution): PFieldReadTerm =
    new PFieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

object PFieldReadTerm {
  def unapply(t: PFieldReadTerm): Option[(PLocation)] =
    Some((t.location))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnfoldingTerm private[silAST]
(override val predicate : PPredicatePermissionExpression, override val term: PTerm)
(sourceLocation: SourceLocation, override val factory: PTermFactory, comment : List[String])
  extends UnfoldingTerm(predicate,term)(sourceLocation,factory,comment)
  with PTerm
{
  override lazy val toString: String = "unfolding " + predicate.toString + " in (" + term.toString + ")"

  override lazy val pSubTerms: Seq[PTerm] = List(predicate.location.receiver,term)

  override def substitute(s: TypeVariableSubstitution): PUnfoldingTerm =
    new PUnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )

  override def substitute(s: LogicalVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )
  override def substitute(s: PLogicalVariableSubstitution): PUnfoldingTerm =
    new PUnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )

  override def substitute(s: ProgramVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )
  override def substitute(s: PProgramVariableSubstitution): PUnfoldingTerm =
    new PUnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation),factory,Nil
    )
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DTerm extends Term
{
  protected def dSubTerms: Seq[DTerm]

  override lazy val subTerms: Seq[DTerm] = dSubTerms

  final override val programVariables = Set[ProgramVariable]()

  override def substitute(s: TypeVariableSubstitution): DTerm

  def substitute(s: DLogicalVariableSubstitution): DTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DIfThenElseTerm
  extends IfThenElseTerm
  with DTerm
{
  override val condition: DTerm = dCondition
  override val pTerm: DTerm = dpTerm
  override val nTerm: DTerm = dnTerm

  protected[silAST] def dCondition: DTerm

  protected[silAST] def dpTerm: DTerm

  protected[silAST] def dnTerm: DTerm

  override def substitute(s: TypeVariableSubstitution): DIfThenElseTerm =
    new DIfThenElseTermC(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: DLogicalVariableSubstitution): DIfThenElseTerm =
    new DIfThenElseTermC(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

object DIfThenElseTerm {
  def unapply(t: DIfThenElseTerm): Option[(DTerm, DTerm, DTerm)] =
    Some((t.condition, t.pTerm, t.nTerm))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
private[silAST] final class DIfThenElseTermC
(override val dCondition: DTerm, override val dpTerm: DTerm, override val dnTerm: DTerm)
(override val sourceLocation: SourceLocation,comment : List[String])
  extends IfThenElseTerm(dCondition, dpTerm, dnTerm)(sourceLocation,comment)
  with DIfThenElseTerm
{
  require(condition.dataType == booleanType)
  require(pTerm.dataType.isCompatible(nTerm.dataType))
  require(nTerm.dataType.isCompatible(pTerm.dataType))

  override val dSubTerms = List(condition, pTerm, nTerm)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class LogicalVariableTerm protected[silAST]
(variable: LogicalVariable)
(override val sourceLocation: SourceLocation,override val comment : List[String])
  extends ASTNode
  with DTerm
  with AtomicTerm
{
  override val toString = variable.name
  override val dSubTerms = Nil

  override def dataType = variable.dataType

  override def freeVariables = Set(variable)

  def substitute(s: TypeVariableSubstitution): LogicalVariableTerm =
    s.mapVariable(variable) match {
      case Some(t: LogicalVariable) => new LogicalVariableTerm(t)(s.sourceLocation(sourceLocation),Nil)
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation),Nil)
    }

  def substitute(s: LogicalVariableSubstitution): Term =
    s.mapVariable(variable) match {
      case Some(t: DTerm) => t
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation),Nil)
    }

  def substitute(s: DLogicalVariableSubstitution): DTerm =
    s.mapVariable(variable) match {
      case Some(t: DTerm) => t
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation),Nil)
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
    new DDomainFunctionApplicationTermC(function.substitute(s), arguments.substitute(s))(s.sourceLocation((sourceLocation)),Nil)

  def substitute(s: DLogicalVariableSubstitution): DDomainFunctionApplicationTerm =
    new DDomainFunctionApplicationTermC(function, arguments.substitute(s))(s.sourceLocation((sourceLocation)),Nil)
}

object DDomainFunctionApplicationTerm {
  def unapply(t: DDomainFunctionApplicationTerm): Option[(DomainFunction, DTermSequence)] =
    Some((t.function, t.arguments))
}


private[silAST] final class DDomainFunctionApplicationTermC
(function: DomainFunction, arguments: DTermSequence)
(sourceLocation: SourceLocation, comment : List[String])
  extends DomainFunctionApplicationTerm(function, arguments)(sourceLocation,comment)
  with DDomainFunctionApplicationTerm
{
  override val dSubTerms = arguments
  override val dArguments = arguments
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domains + Programs = General

sealed trait GTerm extends Term with DTerm with PTerm
{
  override lazy val subTerms: Seq[GTerm] = gSubTerms

  protected def gSubTerms: Seq[GTerm]

  protected override val dSubTerms = gSubTerms
  protected override val pSubTerms = gSubTerms

  def substitute(s: TypeVariableSubstitution): GTerm

  def substitute(s: GLogicalVariableSubstitution): GTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract case class LiteralTerm protected[silAST]
    ()(override val sourceLocation: SourceLocation,override val comment : List[String])
  extends ASTNode with Term
  with GTerm
  with AtomicTerm
{
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class IntegerLiteralTerm private[silAST]
(val value: BigInt)
(sourceLocation: SourceLocation,comment:List[String])
  extends LiteralTerm()(sourceLocation,comment)
  with GTerm
{
  override val toString: String = value.toString()
  override val gSubTerms = Nil

  override def dataType = integerType

  override def substitute(s: TypeVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: LogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PLogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: DLogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: GLogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: ProgramVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: PProgramVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation),Nil)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GDomainFunctionApplicationTerm
(function: DomainFunction, override val arguments: GTermSequence)
(sourceLocation: SourceLocation,comment : List[String])
  extends DomainFunctionApplicationTerm(function, arguments)(sourceLocation,comment)
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
    new GDomainFunctionApplicationTerm(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  def substitute(s: GLogicalVariableSubstitution): GDomainFunctionApplicationTerm =
    new GDomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GIfThenElseTerm private[silAST]
(override val condition: GTerm, override val pTerm: GTerm, override val nTerm: GTerm)
(override val sourceLocation: SourceLocation,comment : List[String])
  extends IfThenElseTerm(condition, pTerm, nTerm)(sourceLocation,comment)
  with PIfThenElseTerm
  with DIfThenElseTerm
  with GTerm
{
  override val pCondition = condition
  override val dCondition = condition
  override val ppTerm = pTerm
  override val dpTerm = pTerm
  override val pnTerm = pTerm
  override val dnTerm = pTerm

  require(condition.dataType == booleanType)
  require(pTerm.dataType.isCompatible(nTerm.dataType))
  require(nTerm.dataType.isCompatible(pTerm.dataType))

  val gSubTerms = List(condition, pTerm, nTerm)

  override def substitute(s: TypeVariableSubstitution): GIfThenElseTerm =
    new GIfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)

  override def substitute(s: GLogicalVariableSubstitution): GIfThenElseTerm =
    new GIfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation),Nil)
}

object GIfThenElseTerm
{
  def unapply(t: GIfThenElseTerm): Option[(GTerm, GTerm, GTerm)] =
    Some((t.condition, t.ppTerm, t.pnTerm))
}

