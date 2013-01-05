package semper.sil.ast.expressions

import scala.collection.Seq

import semper.sil.ast.symbols.logical.quantification.{Quantifier, LogicalVariable}
import semper.sil.ast.symbols.logical.{UnaryConnective, BinaryConnective}
import semper.sil.ast.ASTNode
import terms._
import util.{GTermSequence, TermSequence, PTermSequence, DTermSequence}
import semper.sil.ast.domains._
import semper.sil.ast.types.{TypeVariable, permissionType}
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.programs.symbols.ProgramVariable

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression protected[sil] extends ASTNode {
  def subExpressions: Seq[Expression]

  def freeVariables: Set[LogicalVariable] =
    subExpressions.foldLeft(Set[LogicalVariable]())(_ union _.freeVariables)

  def freeTypeVariables: Set[TypeVariable]

  def programVariables: Set[ProgramVariable]

  override def equals(other: Any): Boolean

  override def hashCode(): Int

  def substitute(s: TypeVariableSubstitution): Expression

  def substitute(s: LogicalVariableSubstitution): Expression

  def substitute(s: ProgramVariableSubstitution): Expression
}


///////////////////////////////////////////////////////////////////////////

sealed trait AtomicExpression extends Expression {
  override val subExpressions: Seq[Expression] = Nil

  //  def freeTypeVariables: Set[TypeVariable] =
  //    subTerms.foldLeft(Set[TypeVariable]())(_ union _.freeTypeVariables)
  def subTerms: Seq[Term]
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PermissionExpression
  extends Expression
  with AtomicExpression {
  def location: Location

  def permission: Term

  require(permission.dataType == permissionType)


  override val programVariables: Set[ProgramVariable] = location.programVariables union permission.programVariables
  override val toString = "acc(" + location.toString + "," + permission.toString + ")"

  override def freeVariables = location.freeVariables ++ permission.freeVariables

  override def substitute(s: TypeVariableSubstitution): PermissionExpression

  override def substitute(s: LogicalVariableSubstitution): PermissionExpression

  override def substitute(s: ProgramVariableSubstitution): PermissionExpression
}

object PermissionExpression {
  def unapply(expr: Expression): Option[(Location, Term)] = expr match {
    case FieldPermissionExpression(location, permission) => Some((location, permission))
    case PredicatePermissionExpression(location, permission) => Some((location, permission))
    case _ => None
  }
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class FieldPermissionExpression private[sil]
(override val location: FieldLocation, override val permission: Term)
(override val sourceLocation: SourceLocation, override val comment: scala.collection.immutable.List[String])
  extends Expression
  with PermissionExpression {
  override def freeTypeVariables: Set[TypeVariable] =
    location.freeTypeVariables union permission.freeTypeVariables

  override val subTerms = location.receiver :: permission :: Nil

  override def substitute(s: TypeVariableSubstitution) =
    new FieldPermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution) =
    new FieldPermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution) =
    new FieldPermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PredicatePermissionExpression private[sil]
(override val location: PredicateLocation, override val permission: Term)
(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression with PermissionExpression {
  override val subTerms = location.receiver :: permission :: Nil

  override def freeTypeVariables: Set[TypeVariable] =
    location.freeTypeVariables union permission.freeTypeVariables

  override def substitute(s: TypeVariableSubstitution) =
    new PredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution) =
    new PredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution) =
    new PredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class OldExpression private[sil]
(expression: Expression)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override val subExpressions = expression :: Nil
  override val toString = "old(" + expression.toString + ")"

  override def freeVariables = expression.freeVariables

  override def freeTypeVariables = expression.freeTypeVariables

  override val programVariables: Set[ProgramVariable] = expression.programVariables

  override def substitute(s: TypeVariableSubstitution): OldExpression =
    new OldExpression(expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): OldExpression =
    new OldExpression(expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): OldExpression =
    new OldExpression(expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingExpression private[sil]
(location: PredicatePermissionExpression, expression: Expression)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override val toString = "unfolding " + location.toString + " in " + expression.toString

  override val subExpressions: Seq[Expression] = List(expression)

  override def freeVariables = location.freeVariables ++ expression.freeVariables

  override def freeTypeVariables = location.freeTypeVariables union expression.freeTypeVariables

  override val programVariables: Set[ProgramVariable] = location.programVariables union expression.programVariables

  override def substitute(s: TypeVariableSubstitution): UnfoldingExpression =
    new UnfoldingExpression(location.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): UnfoldingExpression =
    new UnfoldingExpression(location.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): UnfoldingExpression =
    new UnfoldingExpression(location.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class EqualityExpression private[sil]
(private val t1: Term, private val t2: Term)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  require(t1.dataType.isCompatible(t2.dataType))
  require(t2.dataType.isCompatible(t1.dataType))

  override val toString = t1.toString + "=" + t2.toString

  def term1: Term = t1

  def term2: Term = t2

  override val subExpressions: Seq[Expression] = Nil

  override def freeVariables = term1.freeVariables ++ term2.freeVariables

  override def freeTypeVariables: Set[TypeVariable] = t1.freeTypeVariables union t2.freeTypeVariables

  override def programVariables = term1.programVariables union term2.programVariables

  override def substitute(s: TypeVariableSubstitution): EqualityExpression =
    new EqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): EqualityExpression =
    new EqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): EqualityExpression =
    new EqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnaryExpression private[sil]
(operator: UnaryConnective, operand1: Expression)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override val toString = operator.toString + "(" + operand1.toString + ")"

  override val subExpressions: Seq[Expression] = List(operand1)

  override def freeVariables = operand1.freeVariables

  override def freeTypeVariables = operand1.freeTypeVariables

  override val programVariables = operand1.programVariables

  override def substitute(s: TypeVariableSubstitution): UnaryExpression =
    new UnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): UnaryExpression =
    new UnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): UnaryExpression =
    new UnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class BinaryExpression private[sil]
(operator: BinaryConnective, operand1: Expression, operand2: Expression)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override val toString = operand1.toString + " " + operator.toString + " " + operand2.toString

  override val subExpressions: Seq[Expression] = List(operand1, operand2)

  override def freeVariables = operand1.freeVariables ++ operand2.freeVariables

  override def freeTypeVariables = operand1.freeTypeVariables ++ operand2.freeTypeVariables

  override val programVariables = operand1.programVariables union operand2.programVariables

  override def substitute(s: TypeVariableSubstitution): BinaryExpression =
    new BinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): BinaryExpression =
    new BinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): BinaryExpression =
    new BinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainPredicateExpression private[sil]
(predicate: DomainPredicate, arguments: TermSequence)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression
  with AtomicExpression {
  require((predicate.signature.parameterTypes.zip(arguments).forall((x) => x._2.dataType.isCompatible(x._1))))
  override lazy val toString: String = predicate.toString(arguments)

  override def freeVariables = arguments.freeVariables

  override def freeTypeVariables = arguments.foldLeft(Set[TypeVariable]())(_ union _.freeTypeVariables)

  override val programVariables = arguments.programVariables

  override val subTerms = arguments

  override def substitute(s: TypeVariableSubstitution): DomainPredicateExpression =
    new DomainPredicateExpression(predicate.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): DomainPredicateExpression =
    new DomainPredicateExpression(predicate.substitute(new TypeSubstitutionC[Term](s.types, Set())), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): DomainPredicateExpression =
    new DomainPredicateExpression(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class QuantifierExpression private[sil]
(quantifier: Quantifier, variable: LogicalVariable, expression: Expression)
(val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression {
  override val toString =
    quantifier.toString + " " +
      variable.name + " : " +
      variable.dataType.toString +
      " :: (" + expression.toString + ")"

  override val subExpressions: Seq[Expression] = List(expression)

  override def freeVariables = expression.freeVariables - variable

  override def freeTypeVariables = variable.dataType.freeTypeVariables union expression.freeTypeVariables

  override val programVariables = expression.programVariables

  override def substitute(s: TypeVariableSubstitution): QuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType.substitute(s))(s.sourceLocation((variable.sourceLocation)), Nil)
    val newS = s +
      new TypeSubstitutionC(
        Set(),
        Set((variable, newVar))
      )
    val result = new QuantifierExpression(quantifier, newVar, expression.substitute(newS))(sourceLocation, Nil)
    result
  }

  override def substitute(s: LogicalVariableSubstitution): QuantifierExpression = {
    val ts = new TypeSubstitutionC[Term](s.types, Set())
    val newVar = new LogicalVariable(variable.name, variable.dataType.substitute(ts))(s.sourceLocation((variable.sourceLocation)), Nil)
    val newS = s +
      new LogicalVariableSubstitutionC[Term](
        Set(),
        Set((variable, new LogicalVariableTerm(newVar)(newVar.sourceLocation, Nil)))
      )
    new QuantifierExpression(quantifier, newVar, expression.substitute(newS))(sourceLocation, Nil)
  }

  override def substitute(s: ProgramVariableSubstitution): QuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType)(s.sourceLocation((variable.sourceLocation)), Nil)
    val newS =
      new ProgramVariableSubstitutionC[Term](
        Set(),
        Set((variable, newVar))
      )

    new QuantifierExpression(quantifier, newVar, expression.substitute(newS).substitute(s))(sourceLocation, Nil)
  }
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class TrueExpression()(override val sourceLocation: SourceLocation, override val comment: List[String] = Nil)
  extends Expression
  with AtomicExpression {
  override val toString = "true"
  override val subExpressions = List.empty
  override val programVariables = Set[ProgramVariable]()

  override val subTerms = Nil

  override def freeTypeVariables = Set()

  override def substitute(s: TypeVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class FalseExpression()(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression
  with AtomicExpression {
  override val toString = "false"
  override val subExpressions = List.empty
  override val programVariables = Set[ProgramVariable]()

  override val subTerms = Nil

  override def freeTypeVariables = Set()

  override def substitute(s: TypeVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)
}
