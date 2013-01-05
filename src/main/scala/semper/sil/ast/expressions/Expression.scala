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
//Classification

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Program
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PExpression
  extends Expression {

  override val subExpressions: Seq[PExpression] = pSubExpressions
  final override val freeVariables = Set[LogicalVariable]()

  protected[expressions] def pSubExpressions: Seq[PExpression]

  def substitute(s: TypeVariableSubstitution): PExpression

  def substitute(s: PLogicalVariableSubstitution): PExpression

  def substitute(s: PProgramVariableSubstitution): PExpression
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PEqualityExpression
  extends EqualityExpression
  with PExpression {
  override def term1: PTerm = pTerm1

  override def term2: PTerm = pTerm2

  protected[expressions] def pTerm1: PTerm

  protected[expressions] def pTerm2: PTerm

  override def substitute(s: TypeVariableSubstitution): PEqualityExpression =
    new PEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): PEqualityExpression =
    new PEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): PEqualityExpression =
    new PEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

object PEqualityExpression {
  def unapply(pee: PEqualityExpression): Option[(PTerm, PTerm)] = Some(pee.term1, pee.term2)
}

private[sil] final class PEqualityExpressionC
(term1: PTerm, term2: PTerm)
(sourceLocation: SourceLocation, comment: List[String])
  extends EqualityExpression(term1, term2)(sourceLocation, comment)
  with PEqualityExpression {
  override val pSubExpressions = subExpressions
  override val pTerm1: PTerm = term1
  override val pTerm2: PTerm = term2

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PUnaryExpression extends UnaryExpression with PExpression {
  override val operand1: PExpression = pOperand1

  protected[expressions] def pOperand1: PExpression

  override def substitute(s: TypeVariableSubstitution): PUnaryExpression =
    new PUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): PUnaryExpression =
    new PUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): PUnaryExpression =
    new PUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

object PUnaryExpression {
  def unapply(pube: PUnaryExpression): Option[(UnaryConnective, PExpression)] =
    Some(pube.operator, pube.operand1)
}

private[sil] final class PUnaryExpressionC private[sil]
(override val operator: UnaryConnective, override val operand1: PExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends UnaryExpression(operator, operand1)(sourceLocation, comment)
  with PUnaryExpression {
  override val pSubExpressions: Seq[PExpression] = List(operand1)
  override val pOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PBinaryExpression extends BinaryExpression with PExpression {
  override val operand1: PExpression = pOperand1
  override val operand2: PExpression = pOperand2

  protected[expressions] def pOperand1: PExpression

  protected[expressions] def pOperand2: PExpression

  override def substitute(s: TypeVariableSubstitution): PBinaryExpression =
    new PBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): PBinaryExpression =
    new PBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): PBinaryExpression =
    new PBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

object PBinaryExpression {
  def unapply(pbbe: PBinaryExpression): Option[(BinaryConnective, PExpression, PExpression)] =
    Some(pbbe.operator, pbbe.operand1, pbbe.operand2)
}

private[sil] final class PBinaryExpressionC private[sil]
(override val operator: BinaryConnective, override val operand1: PExpression, override val operand2: PExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends BinaryExpression(operator, operand1, operand2)(sourceLocation, comment)
  with PBinaryExpression {
  override val pSubExpressions: Seq[PExpression] = List(operand1, operand2)
  override val pOperand1 = operand1
  override val pOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainPredicateExpression extends DomainPredicateExpression with PExpression {
  protected[expressions] def pArguments: PTermSequence

  override val arguments: PTermSequence = pArguments

  override def substitute(s: TypeVariableSubstitution): PDomainPredicateExpression =
    new PDomainPredicateExpressionC(predicate.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): PDomainPredicateExpression =
    new PDomainPredicateExpressionC(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): PDomainPredicateExpression =
    new PDomainPredicateExpressionC(predicate.substitute(new TypeSubstitutionC[PTerm](s.types, Set())), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

private[sil] final class PDomainPredicateExpressionC
(override val predicate: DomainPredicate, override val arguments: PTermSequence)
(override val sourceLocation: SourceLocation, comment: List[String])
  extends DomainPredicateExpression(predicate, arguments)(sourceLocation, comment)
  with PDomainPredicateExpression
  with AtomicExpression {
  override val pArguments = arguments
  override val pSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed class PPredicatePermissionExpression private[sil]
(override val location: PPredicateLocation, override val permission: PTerm)
(sourceLocation: SourceLocation, comment: List[String])
  extends PredicatePermissionExpression(location, permission)(sourceLocation, comment)
  with PExpression {
  override val pSubExpressions: scala.collection.immutable.Seq[PExpression] = scala.collection.immutable.List()

  override def substitute(s: TypeVariableSubstitution): PPredicatePermissionExpression =
    new PPredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution) =
    new PredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution) =
    new PPredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution) =
    new PredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution) =
    new PPredicatePermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

object PPredicatePermissionExpression {
  def unapply(e: Expression): Option[(PPredicateLocation, PTerm)] = e match {
    case p: PPredicatePermissionExpression => Some((p.location, p.permission))
    case _ => None
  }
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed class PFieldPermissionExpression private[sil]
(override val location: PFieldLocation, override val permission: PTerm)
(sourceLocation: SourceLocation, comment: List[String])
  extends FieldPermissionExpression(location, permission)(sourceLocation, comment)
  with PExpression {
  override val pSubExpressions: scala.collection.immutable.Seq[PExpression] = scala.collection.immutable.List()

  override def substitute(s: TypeVariableSubstitution): PFieldPermissionExpression =
    new PFieldPermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution) =
    new PFieldPermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution) =
    new PFieldPermissionExpression(location.substitute(s), permission.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnfoldingExpression private[sil]
(override val location: PPredicatePermissionExpression, override val expression: PExpression)
(sourceLocation: SourceLocation, comment: collection.immutable.List[String])
  extends UnfoldingExpression(location, expression)(sourceLocation, comment)
  with PExpression {
  override val pSubExpressions: Seq[PExpression] = List(expression)

  override val programVariables: Set[ProgramVariable] = location.programVariables union expression.programVariables

  override def substitute(s: TypeVariableSubstitution): PUnfoldingExpression =
    new PUnfoldingExpression(location.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): PUnfoldingExpression =
    new PUnfoldingExpression(location.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): PUnfoldingExpression =
    new PUnfoldingExpression(location.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DExpression extends Expression {

  def substitute(s: TypeVariableSubstitution): DExpression

  def substitute(s: DLogicalVariableSubstitution): DExpression

  protected[expressions] def dSubExpressions: Seq[DExpression]

  override val subExpressions: Seq[DExpression] = dSubExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DEqualityExpression
  extends EqualityExpression
  with DExpression {
  protected[expressions] def dTerm1: DTerm

  protected[expressions] def dTerm2: DTerm

  override def term1: DTerm = dTerm1

  override def term2: DTerm = dTerm2

  override def substitute(s: TypeVariableSubstitution): DEqualityExpression =
    new DEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: DLogicalVariableSubstitution): DEqualityExpression =
    new DEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

private[sil] final class DEqualityExpressionC
(term1: DTerm, term2: DTerm)
(sourceLocation: SourceLocation, comment: List[String])
  extends EqualityExpression(term1, term2)(sourceLocation, comment)
  with DEqualityExpression {
  override val dTerm1 = term1
  override val dTerm2 = term2

  override val dSubExpressions = subExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DUnaryExpression extends UnaryExpression with DExpression {
  protected[expressions] def dOperand1: DExpression

  override val operand1: DExpression = dOperand1

  override def substitute(s: TypeVariableSubstitution): DUnaryExpression =
    new DUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: DLogicalVariableSubstitution): DUnaryExpression =
    new DUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

object DUnaryExpression {
  def unapply(dube: DUnaryExpression): Option[(UnaryConnective, DExpression)] =
    Some(dube.operator, dube.operand1)
}

private[sil] final class DUnaryExpressionC private[sil]
(override val operator: UnaryConnective, override val operand1: DExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends UnaryExpression(operator, operand1)(sourceLocation, comment)
  with DUnaryExpression {
  override val dSubExpressions: Seq[DExpression] = List(operand1)
  override val dOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DBinaryExpression extends BinaryExpression with DExpression {
  protected[expressions] def dOperand1: DExpression

  protected[expressions] def dOperand2: DExpression

  override val operand1: DExpression = dOperand1
  override val operand2: DExpression = dOperand2

  override def substitute(s: TypeVariableSubstitution): DBinaryExpression =
    new DBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: DLogicalVariableSubstitution): DBinaryExpression =
    new DBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

object DBinaryExpression {
  def unapply(dbbe: DBinaryExpression): Option[(BinaryConnective, DExpression, DExpression)] =
    Some(dbbe.operator, dbbe.operand1, dbbe.operand2)
}

private[sil] final class DBinaryExpressionC private[sil]
(override val operator: BinaryConnective, override val operand1: DExpression, override val operand2: DExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends BinaryExpression(operator, operand1, operand2)(sourceLocation, comment)
  with DBinaryExpression {
  override val dSubExpressions: Seq[DExpression] = List(operand1, operand2)
  override val dOperand1 = operand1
  override val dOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DDomainPredicateExpression
  extends DomainPredicateExpression
  with DExpression {
  override val arguments: DTermSequence = dArguments

  protected[expressions] def dArguments: DTermSequence

  override def substitute(s: TypeVariableSubstitution): DDomainPredicateExpression =
    new DDomainPredicateExpressionC(predicate.substitute(s), arguments.substitute(s))(sourceLocation, Nil)

  override def substitute(s: DLogicalVariableSubstitution): DDomainPredicateExpression =
    new DDomainPredicateExpressionC(predicate.substitute(new TypeSubstitutionC[DTerm](s.types, Set())), arguments.substitute(s))(sourceLocation, Nil)
}

private[sil] final class DDomainPredicateExpressionC(
                                                      override val predicate: DomainPredicate,
                                                      override val arguments: DTermSequence
                                                      )
                                                    (sourceLocation: SourceLocation, comment: List[String])
  extends DomainPredicateExpression(predicate, arguments)(sourceLocation, comment)
  with DDomainPredicateExpression
  with AtomicExpression {
  override val dArguments = arguments
  override val dSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DQuantifierExpression private[sil]
(override val quantifier: Quantifier, override val variable: LogicalVariable, override val expression: DExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends QuantifierExpression(quantifier, variable, expression)(sourceLocation, comment)
  with DExpression {
  override val subExpressions: Seq[DExpression] = List(expression)
  override val dSubExpressions = subExpressions

  override def substitute(s: TypeVariableSubstitution): DQuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType.substitute(s))(s.sourceLocation(variable.sourceLocation), Nil)
    val newS = s + new TypeSubstitutionC(Set(), Set((variable, newVar)))
    val result = new DQuantifierExpression(quantifier, newVar, expression.substitute(newS))(s.sourceLocation(sourceLocation), Nil)
    result
  }

  override def substitute(s: DLogicalVariableSubstitution): DQuantifierExpression = {
    val ts = new TypeSubstitutionC[Term](s.types, Set())
    val newVar = new LogicalVariable(variable.name, variable.dataType.substitute(ts))(s.sourceLocation(variable.sourceLocation), Nil)
    val newS = s + new DLogicalVariableSubstitutionC(
      s.types,
      Set((variable, new LogicalVariableTerm(newVar)(newVar.sourceLocation, Nil)))
    )
    new DQuantifierExpression(quantifier, newVar, expression.substitute(newS))(s.sourceLocation(sourceLocation), Nil)
  }

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//General/ground
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait GExpression
  extends Expression with DExpression with PExpression {
  override val subExpressions: Seq[GExpression] = gSubExpressions
  protected[expressions] final override val pSubExpressions = subExpressions
  protected[expressions] final override val dSubExpressions = subExpressions

  override val programVariables = Set[ProgramVariable]()

  protected[expressions] def gSubExpressions: Seq[GExpression]

  def substitute(s: TypeVariableSubstitution): GExpression

  def substitute(s: GLogicalVariableSubstitution): GExpression
}

///////////////////////////////////////////////////////////////////////////
final class GEqualityExpression private[sil]
(override val term1: GTerm, override val term2: GTerm)
(sourceLocation: SourceLocation, comment: List[String])
  extends EqualityExpression(term1, term2)(sourceLocation, comment)
  with PEqualityExpression
  with DEqualityExpression
  with GExpression {
  override val subExpressions: Seq[GExpression] = Nil
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pTerm1 = term1
  protected[expressions] override val pTerm2 = term2
  protected[expressions] override val dTerm1 = term1
  protected[expressions] override val dTerm2 = term2

  override def substitute(s: TypeVariableSubstitution): GEqualityExpression =
    new GEqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: GLogicalVariableSubstitution): GEqualityExpression =
    new GEqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GUnaryExpression private[sil]
(operator: UnaryConnective, override val operand1: GExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends UnaryExpression(operator, operand1)(sourceLocation, comment)
  with PUnaryExpression
  with DUnaryExpression
  with GExpression {
  override val subExpressions = List(operand1)
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1

  override def substitute(s: TypeVariableSubstitution): GUnaryExpression =
    new GUnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: GLogicalVariableSubstitution): GUnaryExpression =
    new GUnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GBinaryExpression private[sil]
(operator: BinaryConnective, override val operand1: GExpression, override val operand2: GExpression)
(sourceLocation: SourceLocation, comment: List[String])
  extends BinaryExpression(operator, operand1, operand2)(sourceLocation, comment)
  with PBinaryExpression
  with DBinaryExpression
  with GExpression {

  override val subExpressions = List(operand1, operand2)

  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1
  protected[expressions] override val pOperand2 = operand2
  protected[expressions] override val dOperand2 = operand2

  override def substitute(s: TypeVariableSubstitution): GBinaryExpression =
    new GBinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: GLogicalVariableSubstitution): GBinaryExpression =
    new GBinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GDomainPredicateExpression private[sil]
(predicate: DomainPredicate, override val arguments: GTermSequence)
(sourceLocation: SourceLocation, comment: List[String])
  extends DomainPredicateExpression(predicate, arguments)(sourceLocation, comment)
  with PDomainPredicateExpression
  with DDomainPredicateExpression
  with GExpression {
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val dArguments = arguments
  protected[expressions] override val pArguments = arguments

  override def substitute(s: TypeVariableSubstitution): GDomainPredicateExpression =
    new GDomainPredicateExpression(predicate.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: GLogicalVariableSubstitution): GDomainPredicateExpression =
    new GDomainPredicateExpression(predicate.substitute(new TypeSubstitutionC[GTerm](s.types, Set())), arguments.substitute(s))(s.sourceLocation(sourceLocation), Nil)
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class TrueExpression()(override val sourceLocation: SourceLocation, override val comment: List[String] = Nil)
  extends Expression
  with GExpression
  with AtomicExpression {
  override val toString = "true"
  override val subExpressions = List.empty
  override val gSubExpressions = List.empty

  override val subTerms = Nil

  override def freeTypeVariables = Set()

  override def substitute(s: TypeVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: DLogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: GLogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation), Nil)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class FalseExpression()(override val sourceLocation: SourceLocation, override val comment: List[String])
  extends Expression
  with GExpression
  with AtomicExpression {
  override val toString = "false"
  override val subExpressions = List.empty
  override val gSubExpressions = List.empty

  override val subTerms = Nil

  override def freeTypeVariables = Set()

  override def substitute(s: TypeVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: LogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: DLogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PLogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: GLogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: ProgramVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)

  override def substitute(s: PProgramVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation), Nil)
}
