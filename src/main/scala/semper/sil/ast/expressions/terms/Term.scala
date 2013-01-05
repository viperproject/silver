package semper.sil.ast.expressions.terms

import semper.sil.ast.symbols.logical.quantification.LogicalVariable
import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.util.{GTermSequence, DTermSequence, PTermSequence, TermSequence}
import semper.sil.ast.programs.symbols.{Predicate, ProgramVariable, Field, Function}
import semper.sil.ast.domains._
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.types._
import semper.sil.ast.expressions.{PredicatePermissionExpression, ProgramVariableSubstitution}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Location
  extends ASTNode {
  override val sourceLocation = receiver.sourceLocation
  override val comment = Nil

  def receiver: Term

  def dataType: DataType

  require(receiver.dataType == referenceType)

  def freeVariables: collection.immutable.Set[LogicalVariable]

  def freeTypeVariables: collection.immutable.Set[TypeVariable]

  def programVariables: collection.immutable.Set[ProgramVariable]

  def substitute(s: TypeVariableSubstitution): Location

  def substitute(s: LogicalVariableSubstitution): Location

  def substitute(s: ProgramVariableSubstitution): Location
}

sealed case class FieldLocation private[sil](receiver: Term, field: Field) extends Location {
  override val toString = receiver.toString + "." + field.name
  override lazy val dataType = field.dataType

  override def freeVariables = receiver.freeVariables

  override def freeTypeVariables = receiver.freeTypeVariables union field.dataType.freeTypeVariables

  override def programVariables = receiver.programVariables

  def substitute(s: TypeVariableSubstitution): FieldLocation =
    new FieldLocation(receiver.substitute(s), field)

  def substitute(s: LogicalVariableSubstitution): FieldLocation =
    new FieldLocation(receiver.substitute(s), field)

  def substitute(s: ProgramVariableSubstitution): FieldLocation =
    new FieldLocation(receiver.substitute(s), field)
}

sealed case class PredicateLocation private[sil](receiver: Term, predicate: Predicate)
  extends Location {
  override val toString = receiver.toString + "." + predicate.name
  override lazy val dataType = booleanType

  override def freeVariables = receiver.freeVariables

  override def freeTypeVariables = receiver.freeTypeVariables

  override def programVariables = receiver.programVariables

  def substitute(s: TypeVariableSubstitution): PredicateLocation =
    new PredicateLocation(receiver.substitute(s), predicate)

  def substitute(s: LogicalVariableSubstitution): PredicateLocation =
    new PredicateLocation(receiver.substitute(s), predicate)

  def substitute(s: ProgramVariableSubstitution): PredicateLocation =
    new PredicateLocation(receiver.substitute(s), predicate)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait Term extends ASTNode {
  def subTerms: Seq[Term]

  def dataType: DataType

  def freeVariables: collection.immutable.Set[LogicalVariable]

  def freeTypeVariables: collection.immutable.Set[TypeVariable]

  def programVariables: collection.immutable.Set[ProgramVariable]

  def substitute(s: TypeVariableSubstitution): Term

  def substitute(s: LogicalVariableSubstitution): Term

  def substitute(s: ProgramVariableSubstitution): Term
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait AtomicTerm extends Term {
  final override lazy val subTerms: Seq[Term] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Assertion terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class IfThenElseTerm private[sil]
(condition: Term, pTerm: Term, nTerm: Term)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Term {
  require(condition.dataType == booleanType)
  require(pTerm.dataType.isCompatible(nTerm.dataType))
  require(nTerm.dataType.isCompatible(pTerm.dataType))

  override val dataType = pTerm.dataType
  override val freeVariables = condition.freeVariables ++ pTerm.freeVariables ++ nTerm.freeVariables
  override val freeTypeVariables = condition.freeTypeVariables union pTerm.freeTypeVariables union nTerm.freeTypeVariables

  override val programVariables = condition.programVariables ++ pTerm.programVariables ++ nTerm.programVariables
  override lazy val subTerms: Seq[Term] = List(condition, pTerm, nTerm)

  def substitute(s: TypeVariableSubstitution): IfThenElseTerm =
    new IfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): IfThenElseTerm =
    new IfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): IfThenElseTerm =
    new IfThenElseTerm(condition.substitute(s), pTerm.substitute(s), nTerm.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

sealed case class OldTerm private[sil]
(term: Term)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode
  with Term {
  override val toString: String = "old(" + term.toString + ")"

  override val subTerms: Seq[Term] = List(term)

  override def dataType = term.dataType

  override def freeVariables = term.freeVariables

  override val freeTypeVariables = term.freeTypeVariables

  override def programVariables = term.programVariables

  def substitute(s: TypeVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): OldTerm =
    new OldTerm(term.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationTerm private[sil]
(private val f: DomainFunction, private val as: TermSequence)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode with Term {
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

  override lazy val freeTypeVariables = arguments.freeTypeVariables

  override def programVariables = arguments.programVariables

  def substitute(s: TypeVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function.substitute(new TypeSubstitutionC[Term](s.types, Set())), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): DomainFunctionApplicationTerm =
    new DomainFunctionApplicationTerm(function, arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FunctionApplicationTerm private[sil]
(receiver: Term, function: Function, arguments: TermSequence)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode with Term {
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

  override val freeTypeVariables = receiver.freeTypeVariables union function.freeTypeVariables union arguments.freeTypeVariables

  override def programVariables = arguments.programVariables ++ receiver.programVariables

  def substitute(s: TypeVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): FunctionApplicationTerm =
    new FunctionApplicationTerm(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingTerm private[sil]
(predicate: PredicatePermissionExpression, term: Term)
(override val sourceLocation: SourceLocation, val factory: TermFactory, override val comment: List[String])
  extends ASTNode with Term {
  override lazy val toString: String = "unfolding " + predicate.toString + " in (" + term.toString + ")"

  override lazy val subTerms: Seq[Term] = List(predicate.location.receiver, term)

  override def dataType = term.dataType

  override def freeVariables = predicate.freeVariables ++ term.freeVariables

  override val freeTypeVariables = predicate.freeTypeVariables union term.freeTypeVariables

  override def programVariables = predicate.programVariables ++ term.programVariables

  def substitute(s: TypeVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation), factory, Nil
    )

  def substitute(s: LogicalVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation), factory, Nil
    )

  def substitute(s: ProgramVariableSubstitution): UnfoldingTerm =
    new UnfoldingTerm(predicate.substitute(s), term.substitute(s))(
      s.sourceLocation(sourceLocation), factory, Nil
    )
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class CastTerm protected[sil]
(operand1: Term, newType: DataType)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode with Term {
  override val toString: String = "(" + operand1 + ") : " + newType.toString

  override lazy val subTerms: Seq[Term] = operand1 :: Nil

  override def dataType = newType

  override def freeVariables = operand1.freeVariables

  override val freeTypeVariables = operand1.freeTypeVariables union newType.freeTypeVariables

  override def programVariables = operand1.programVariables

  def substitute(s: TypeVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): CastTerm =
    new CastTerm(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation), Nil)
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldReadTerm protected[sil]
(location: FieldLocation)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode with Term {
  override lazy val toString: String = location.toString
  override lazy val subTerms: Seq[Term] = List(location.receiver)

  override lazy val dataType = location.dataType

  override def freeVariables = location.freeVariables

  override val freeTypeVariables = location.freeTypeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): FieldReadTerm =
    new FieldReadTerm(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PermTerm protected[sil]
(location: Location)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode with Term {
  override lazy val toString: String = "perm(" + location.toString + ")"
  override lazy val subTerms: Seq[Term] = List(location.receiver)

  override lazy val dataType = permissionType

  override def freeVariables = location.freeVariables

  override val freeTypeVariables = location.freeTypeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): PermTerm =
    new PermTerm(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FullPermissionTerm()
                             (sourceLocation: SourceLocation, comment: List[String])
  extends LiteralTerm()(sourceLocation, comment)
  with AtomicTerm {
  override def toString: String = "write"

  override val subTerms = Nil
  override val dataType = permissionType

  override val freeTypeVariables = collection.immutable.Set[TypeVariable]()

  override def substitute(s: TypeVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): FullPermissionTerm = new FullPermissionTerm()(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class NoPermissionTerm()
                           (sourceLocation: SourceLocation, comment: List[String])
  extends LiteralTerm()(sourceLocation, comment)
  with AtomicTerm {
  override def toString: String = "0"

  override val freeTypeVariables = collection.immutable.Set[TypeVariable]()

  override val subTerms = Seq()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): NoPermissionTerm = new NoPermissionTerm()(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class EpsilonPermissionTerm()
                                (sourceLocation: SourceLocation, comment: List[String])
  extends LiteralTerm()(sourceLocation, comment)
  with AtomicTerm {
  override def toString: String = "E"

  override val freeTypeVariables = collection.immutable.Set[TypeVariable]()

  override val subTerms = Seq()
  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): EpsilonPermissionTerm = new EpsilonPermissionTerm()(s.sourceLocation(sourceLocation), Nil)
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

  final override val freeVariables = Set[LogicalVariable]()

  def substitute(s: TypeVariableSubstitution): PTerm
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableTerm protected[sil]
(variable: ProgramVariable)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode
  with PTerm
  with AtomicTerm {
  override val toString: String = variable.name
  override val pSubTerms = Nil

  override def dataType = variable.dataType

  override def programVariables = Set(variable)

  override def freeTypeVariables = variable.dataType.freeTypeVariables

  def substitute(s: TypeVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): ProgramVariableTerm = new ProgramVariableTerm(variable)(s.sourceLocation(sourceLocation), Nil)

  //Must have mapping
  def substitute(s: ProgramVariableSubstitution): Term = s.mapVariable(variable).get
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class LogicalVariableTerm protected[sil]
(variable: LogicalVariable)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode
  with Term
  with AtomicTerm {
  override val toString = variable.name
  override val subTerms = Nil

  override def dataType = variable.dataType

  override def freeVariables = Set(variable)

  override val programVariables: Set[ProgramVariable] = Set()

  override def freeTypeVariables = variable.dataType.freeTypeVariables

  def substitute(s: TypeVariableSubstitution): LogicalVariableTerm =
    s.mapVariable(variable) match {
      case Some(t: LogicalVariable) => new LogicalVariableTerm(t)(s.sourceLocation(sourceLocation), Nil)
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation), Nil)
    }

  def substitute(s: LogicalVariableSubstitution): Term =
    s.mapVariable(variable) match {
      case Some(t: Term) => t
      case _ => new LogicalVariableTerm(variable)(s.sourceLocation(sourceLocation), Nil)
    }

  def substitute(s: ProgramVariableSubstitution): Term =
    this

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class LiteralTerm protected[sil]
()(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends ASTNode with Term
  with AtomicTerm {
  override val  freeVariables: Set[LogicalVariable] = Set()
  override val  programVariables: Set[ProgramVariable] = Set()
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class IntegerLiteralTerm private[sil]
(val value: BigInt)
(sourceLocation: SourceLocation, comment: List[String])
  extends LiteralTerm()(sourceLocation, comment)
  with Term {
  override val toString: String = value.toString()
  override val subTerms = Nil

  override def dataType = integerType

  override def freeTypeVariables = collection.immutable.Set()

  override def equals(other: Any) = {
    other match {
      case ilt: IntegerLiteralTerm => value.equals(ilt.value)
      case _ => false
    }
  }

  override val hashCode = value.hashCode()

  override def substitute(s: TypeVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): IntegerLiteralTerm =
    new IntegerLiteralTerm(value)(s.sourceLocation(sourceLocation), Nil)
}
