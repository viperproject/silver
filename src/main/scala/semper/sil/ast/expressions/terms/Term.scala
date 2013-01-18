package semper.sil.ast.expressions.terms

import semper.sil.ast.symbols.logical.quantification.LogicalVariable
import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.util.ExpressionSequence
import semper.sil.ast.programs.symbols.{Predicate, ProgramVariable, Field, Function}
import semper.sil.ast.domains._
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.types._
import semper.sil.ast.expressions.{Expression, PredicatePermissionExpression, ProgramVariableSubstitution}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Location
  extends ASTNode {
  override val sourceLocation = receiver.sourceLocation
  override val comment = Nil

  def receiver: Expression

  def dataType: DataType

  require(receiver.dataType == referenceType)

  def freeVariables: collection.immutable.Set[LogicalVariable]

  def freeTypeVariables: collection.immutable.Set[TypeVariable]

  def programVariables: collection.immutable.Set[ProgramVariable]

  def substitute(s: TypeVariableSubstitution): Location

  def substitute(s: LogicalVariableSubstitution): Location

  def substitute(s: ProgramVariableSubstitution): Location
}

sealed case class FieldLocation private[sil](receiver: Expression, field: Field) extends Location {
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

sealed case class PredicateLocation private[sil](receiver: Expression, predicate: Predicate)
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
sealed trait AtomicExpression extends Expression {
  final override lazy val subExpressions: Seq[Expression] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Assertion terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class IfThenElseExpression private[sil]
(condition: Expression, pExpression: Expression, nExpression: Expression)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  require(condition.dataType == booleanType)
  require(pExpression.dataType.isCompatible(nExpression.dataType))
  require(nExpression.dataType.isCompatible(pExpression.dataType))

  override val dataType = pExpression.dataType
  override val freeVariables = condition.freeVariables ++ pExpression.freeVariables ++ nExpression.freeVariables
  override val freeTypeVariables = condition.freeTypeVariables union pExpression.freeTypeVariables union nExpression.freeTypeVariables

  override val programVariables = condition.programVariables ++ pExpression.programVariables ++ nExpression.programVariables
  override lazy val subExpressions: Seq[Expression] = List(condition, pExpression, nExpression)

  def substitute(s: TypeVariableSubstitution): IfThenElseExpression =
    new IfThenElseExpression(condition.substitute(s), pExpression.substitute(s), nExpression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): IfThenElseExpression =
    new IfThenElseExpression(condition.substitute(s), pExpression.substitute(s), nExpression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): IfThenElseExpression =
    new IfThenElseExpression(condition.substitute(s), pExpression.substitute(s), nExpression.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainFunctionApplicationExpression private[sil]
(private val f: DomainFunction, private val as: ExpressionSequence)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
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

  override lazy val subExpressions: Seq[Expression] = arguments

  def function: DomainFunction = f

  def arguments: ExpressionSequence = as

  override def dataType = function.signature.resultType

  override def freeVariables = arguments.freeVariables

  override lazy val freeTypeVariables = arguments.freeTypeVariables

  override def programVariables = arguments.programVariables

  def substitute(s: TypeVariableSubstitution): DomainFunctionApplicationExpression =
    new DomainFunctionApplicationExpression(function.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): DomainFunctionApplicationExpression =
    new DomainFunctionApplicationExpression(function.substitute(new TypeSubstitutionC[Expression](s.types, Set())), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): DomainFunctionApplicationExpression =
    new DomainFunctionApplicationExpression(function, arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FunctionApplicationExpression private[sil]
(receiver: Expression, function: Function, arguments: ExpressionSequence)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression  {
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

  override lazy val subExpressions: Seq[Expression] = List(receiver) ++ arguments.toList

  override def dataType = function.signature.result.dataType

  override def freeVariables = arguments.freeVariables ++ receiver.freeVariables

  override val freeTypeVariables = receiver.freeTypeVariables union function.freeTypeVariables union arguments.freeTypeVariables

  override def programVariables = arguments.programVariables ++ receiver.programVariables

  def substitute(s: TypeVariableSubstitution): FunctionApplicationExpression =
    new FunctionApplicationExpression(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): FunctionApplicationExpression =
    new FunctionApplicationExpression(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): FunctionApplicationExpression =
    new FunctionApplicationExpression(receiver.substitute(s), function, arguments.substitute(s))(
      s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Heap related terms

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class CastExpression protected[sil]
(operand1: Expression, newType: DataType)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override val toString: String = "(" + operand1 + ") : " + newType.toString

  override lazy val subExpressions: Seq[Expression] = operand1 :: Nil

  override def dataType = newType

  override def freeVariables = operand1.freeVariables

  override val freeTypeVariables = operand1.freeTypeVariables union newType.freeTypeVariables

  override def programVariables = operand1.programVariables

  def substitute(s: TypeVariableSubstitution): CastExpression =
    new CastExpression(operand1.substitute(s), newType.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): CastExpression =
    new CastExpression(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): CastExpression =
    new CastExpression(operand1.substitute(s), newType)(s.sourceLocation(sourceLocation), Nil)
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldReadExpression protected[sil]
(location: FieldLocation)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override lazy val toString: String = location.toString
  override lazy val subExpressions: Seq[Expression] = List(location.receiver)

  override lazy val dataType = location.dataType

  override def freeVariables = location.freeVariables

  override val freeTypeVariables = location.freeTypeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): FieldReadExpression =
    new FieldReadExpression(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): FieldReadExpression =
    new FieldReadExpression(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): FieldReadExpression =
    new FieldReadExpression(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PermExpression protected[sil]
(location: Location)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override lazy val toString: String = "perm(" + location.toString + ")"
  override lazy val subExpressions: Seq[Expression] = List(location.receiver)

  override lazy val dataType = permissionType

  override def freeVariables = location.freeVariables

  override val freeTypeVariables = location.freeTypeVariables

  override def programVariables = location.programVariables

  def substitute(s: TypeVariableSubstitution): PermExpression =
    new PermExpression(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): PermExpression =
    new PermExpression(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: ProgramVariableSubstitution): PermExpression =
    new PermExpression(location.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class FullPermissionExpression()
                             (sourceLocation: SourceLocation, comment: List[String])
  extends LiteralExpression()(sourceLocation, comment)
  with AtomicExpression {
  override def toString: String = "write"

  override val dataType = permissionType

  override val freeTypeVariables = collection.immutable.Set[TypeVariable]()

  override def substitute(s: TypeVariableSubstitution): FullPermissionExpression = new FullPermissionExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): FullPermissionExpression = new FullPermissionExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): FullPermissionExpression = new FullPermissionExpression()(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class NoPermissionExpression()
                           (sourceLocation: SourceLocation, comment: List[String])
  extends LiteralExpression()(sourceLocation, comment)
  with AtomicExpression {
  override def toString: String = "0"

  override val freeTypeVariables = collection.immutable.Set[TypeVariable]()

  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): NoPermissionExpression = new NoPermissionExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): NoPermissionExpression = new NoPermissionExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): NoPermissionExpression = new NoPermissionExpression()(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
case class EpsilonPermissionExpression()
                                (sourceLocation: SourceLocation, comment: List[String])
  extends LiteralExpression()(sourceLocation, comment)
  with AtomicExpression {
  override def toString: String = "E"

  override val freeTypeVariables = collection.immutable.Set[TypeVariable]()

  override val dataType = permissionType

  override def substitute(s: TypeVariableSubstitution): EpsilonPermissionExpression = new EpsilonPermissionExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): EpsilonPermissionExpression = new EpsilonPermissionExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): EpsilonPermissionExpression = new EpsilonPermissionExpression()(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class ProgramVariableExpression protected[sil]
(variable: ProgramVariable)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression
  with AtomicExpression {
  override val toString: String = variable.name

  override def dataType = variable.dataType

  override def programVariables = Set(variable)

  override val freeVariables = Set[LogicalVariable]()

  override def freeTypeVariables = variable.dataType.freeTypeVariables

  def substitute(s: TypeVariableSubstitution): ProgramVariableExpression = new ProgramVariableExpression(variable)(s.sourceLocation(sourceLocation), Nil)

  def substitute(s: LogicalVariableSubstitution): ProgramVariableExpression = new ProgramVariableExpression(variable)(s.sourceLocation(sourceLocation), Nil)

  //Must have mapping
  def substitute(s: ProgramVariableSubstitution): Expression = s.mapVariable(variable).get
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Quantification terms
sealed case class LogicalVariableExpression protected[sil]
(variable: LogicalVariable)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression
  with AtomicExpression {
  override val toString = variable.name

  override def dataType = variable.dataType

  override def freeVariables = Set(variable)

  override val programVariables: Set[ProgramVariable] = Set()

  override def freeTypeVariables = variable.dataType.freeTypeVariables

  def substitute(s: TypeVariableSubstitution): LogicalVariableExpression =
    s.mapVariable(variable) match {
      case Some(t: LogicalVariable) => new LogicalVariableExpression(t)(s.sourceLocation(sourceLocation), Nil)
      case _ => new LogicalVariableExpression(variable)(s.sourceLocation(sourceLocation), Nil)
    }

  def substitute(s: LogicalVariableSubstitution): Expression =
    s.mapVariable(variable) match {
      case Some(t: Expression) => t
      case _ => new LogicalVariableExpression(variable)(s.sourceLocation(sourceLocation), Nil)
    }

  def substitute(s: ProgramVariableSubstitution): Expression =
    this

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class LiteralExpression protected[sil]
()(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression
  with AtomicExpression {
  override val  freeVariables: Set[LogicalVariable] = Set()
  override val  programVariables: Set[ProgramVariable] = Set()
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class IntegerLiteralExpression private[sil]
(value: BigInt)
(sourceLocation: SourceLocation, comment: List[String])
  extends LiteralExpression()(sourceLocation, comment) {
  override val toString: String = value.toString()

  override def dataType = integerType

  override def freeTypeVariables = collection.immutable.Set()

  override def equals(other: Any) = {
    other match {
      case ilt: IntegerLiteralExpression => value.equals(ilt.value)
      case _ => false
    }
  }

  override val hashCode = value.hashCode()

  override def substitute(s: TypeVariableSubstitution): IntegerLiteralExpression =
    new IntegerLiteralExpression(value)(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): IntegerLiteralExpression =
    new IntegerLiteralExpression(value)(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): IntegerLiteralExpression =
    new IntegerLiteralExpression(value)(s.sourceLocation(sourceLocation), Nil)
}
