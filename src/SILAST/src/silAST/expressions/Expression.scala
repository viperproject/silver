package silAST.expressions

import scala.collection.Seq

import silAST.symbols.logical.quantification.{Quantifier, LogicalVariable}
import silAST.symbols.logical.{UnaryConnective, BinaryConnective}
import silAST.ASTNode
import terms._
import util.{GTermSequence, TermSequence, PTermSequence, DTermSequence}
import silAST.domains._
import silAST.types.{referenceType, permissionType}
import silAST.programs.symbols.{Field, Predicate}
import silAST.source.SourceLocation

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed abstract class Expression protected[silAST] extends ASTNode {
  def subExpressions: Seq[Expression]
  def freeVariables: Set[LogicalVariable]

  override def equals(other : Any) : Boolean
  override def hashCode() : Int

  def substitute(s: TypeVariableSubstitution): Expression
  def substitute(s: LogicalVariableSubstitution): Expression
  def substitute(s: ProgramVariableSubstitution): Expression
}


///////////////////////////////////////////////////////////////////////////

sealed trait AtomicExpression extends Expression {
  override val subExpressions: Seq[Expression] = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class PermissionExpression private[silAST]
    (reference: Term,field : Field,permission: Term)
    (val sourceLocation : SourceLocation)
  extends Expression
  with AtomicExpression
{
  require(reference.dataType == referenceType)
  require(permission.dataType == permissionType)

  override val toString = "acc(" + reference.toString + "." + field.name + "," + permission.toString + ")"

  override def freeVariables = reference.freeVariables ++ permission.freeVariables

  override def substitute(s: TypeVariableSubstitution) =
    new PermissionExpression(reference.substitute(s), field, permission.substitute(s))(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution) =
    new PermissionExpression(reference.substitute(s), field, permission.substitute(s))(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution) =
    new PermissionExpression(reference.substitute(s), field, permission.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class OldExpression private[silAST]
    (expression: Expression)
    (val sourceLocation : SourceLocation)
  extends Expression
  with AtomicExpression
{
  override val toString = "old(" + expression.toString + ")"

  override def freeVariables = expression.freeVariables

  override def substitute(s: TypeVariableSubstitution): OldExpression =
    new OldExpression(expression.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): OldExpression =
    new OldExpression(expression.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): OldExpression =
    new OldExpression(expression.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnfoldingExpression private[silAST]
    (predicate: PredicateExpression,expression: Expression)
    (val sourceLocation : SourceLocation)
  extends Expression
{
  override val toString = "unfolding " + predicate.toString + " in " + expression.toString

  override val subExpressions: Seq[Expression] = List(expression)

  override def freeVariables = predicate.freeVariables ++ expression.freeVariables

  override def substitute(s: TypeVariableSubstitution): UnfoldingExpression =
    new UnfoldingExpression(predicate.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): UnfoldingExpression =
    new UnfoldingExpression(predicate.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): UnfoldingExpression =
    new UnfoldingExpression(predicate.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class EqualityExpression private[silAST]
    (private val t1: Term,private val t2: Term)
    (val sourceLocation : SourceLocation)
  extends Expression
{
  require (t1.dataType.isCompatible(t2.dataType))
  require (t2.dataType.isCompatible(t1.dataType))

  override val toString = t1.toString + "=" + t2.toString

  def term1: Term = t1

  def term2: Term = t2

  override val subExpressions: Seq[Expression] = Nil

  override def freeVariables = term1.freeVariables ++ term2.freeVariables

  override def substitute(s: TypeVariableSubstitution): EqualityExpression =
    new EqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): EqualityExpression =
    new EqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): EqualityExpression =
    new EqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class UnaryExpression private[silAST]
    (operator: UnaryConnective,operand1: Expression)
    (val sourceLocation : SourceLocation)
  extends Expression
{
  override val toString = operator.toString + operand1.toString

  override val subExpressions: Seq[Expression] = List(operand1)

  override def freeVariables = operand1.freeVariables

  override def substitute(s: TypeVariableSubstitution): UnaryExpression =
    new UnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): UnaryExpression =
    new UnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): UnaryExpression =
    new UnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class BinaryExpression private[silAST]
    (operator: BinaryConnective,operand1: Expression,operand2: Expression)
    (val sourceLocation : SourceLocation)
  extends Expression
{
  override val toString = operand1.toString + " " + operator.toString + " " + operand2.toString

  override val subExpressions: Seq[Expression] = List(operand1, operand2)

  override def freeVariables = operand1.freeVariables ++ operand2.freeVariables

  override def substitute(s: TypeVariableSubstitution): BinaryExpression =
    new BinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): BinaryExpression =
    new BinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): BinaryExpression =
    new BinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class DomainPredicateExpression private[silAST]
    (predicate: DomainPredicate,arguments: TermSequence)
    (val sourceLocation : SourceLocation)
  extends Expression
  with AtomicExpression
{
  require((predicate.signature.parameterTypes.zip(arguments).forall((x)=>x._2.dataType.isCompatible(x._1))))
  override lazy val toString: String = predicate.toString(arguments)

  override def freeVariables = arguments.freeVariables

  override def substitute(s: TypeVariableSubstitution): DomainPredicateExpression =
    new DomainPredicateExpression(predicate.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): DomainPredicateExpression =
    new DomainPredicateExpression(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): DomainPredicateExpression =
    new DomainPredicateExpression(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class PredicateExpression private[silAST]
    (receiver: Term,predicate: Predicate)
    (val sourceLocation : SourceLocation)
  extends Expression
  with AtomicExpression
{
  require (receiver.dataType == referenceType)
  override val toString = receiver + "." + predicate.name

  override def freeVariables = receiver.freeVariables //TODO:Can receiver have free variables?
  override def substitute(s: TypeVariableSubstitution): PredicateExpression =
    new PredicateExpression(receiver.substitute(s), predicate)(s.sourceLocation(sourceLocation))
  override def substitute(s: LogicalVariableSubstitution): PredicateExpression =
    new PredicateExpression(receiver.substitute(s), predicate)(s.sourceLocation(sourceLocation))
  override def substitute(s: ProgramVariableSubstitution): PredicateExpression =
    new PredicateExpression(receiver.substitute(s), predicate)(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed case class QuantifierExpression private[silAST]
    (quantifier: Quantifier,variable: LogicalVariable,expression: Expression)
    (val sourceLocation : SourceLocation)
  extends Expression
{
  override val toString =
    quantifier.toString + " " +
      variable.name + " : " +
      variable.dataType.toString +
      " :: (" + expression.toString + ")"

  override val subExpressions: Seq[Expression] = List(expression)

  override def freeVariables = expression.freeVariables - variable

  override def substitute(s: TypeVariableSubstitution): QuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType.substitute(s))(s.sourceLocation((variable.sourceLocation)))
    val newS = s +
      new TypeSubstitutionC(
        Set(),
        Set((variable, newVar)),
        (newVar.sourceLocation),
        s.newDomain
      )
    new QuantifierExpression(quantifier, newVar, expression.substitute(newS))(sourceLocation)
  }
  override def substitute(s: LogicalVariableSubstitution): QuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType)(s.sourceLocation((variable.sourceLocation)))
    val newS = s +
      new LogicalVariableSubstitutionC[Term](
        Set(),
        Set((variable, new LogicalVariableTerm(newVar)(newVar.sourceLocation)))
      )
    new QuantifierExpression(quantifier, newVar, expression.substitute(newS))(sourceLocation)
  }

  override def substitute(s: ProgramVariableSubstitution): QuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType)(s.sourceLocation((variable.sourceLocation)))
    val newS =
      new ProgramVariableSubstitutionC[Term](
        s.targetFactory,
        Set(),
        Set((variable, newVar))
      )

    new QuantifierExpression(quantifier, newVar, expression.substitute(newS).substitute(s))(sourceLocation)
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
  extends Expression
{

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
  with PExpression
{
  override def term1: PTerm = pTerm1

  override def term2: PTerm = pTerm2

  protected[expressions] def pTerm1: PTerm

  protected[expressions] def pTerm2: PTerm

  override def substitute(s: TypeVariableSubstitution): PEqualityExpression =
    new PEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): PEqualityExpression =
    new PEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): PEqualityExpression =
    new PEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
}

object PEqualityExpression {
  def unapply(pee: PEqualityExpression): Option[(PTerm, PTerm)] = Some(pee.term1, pee.term2)
}

private[silAST] final class PEqualityExpressionC
    (term1: PTerm,term2: PTerm)
    (sourceLocation : SourceLocation)
  extends EqualityExpression(term1, term2)(sourceLocation)
  with PEqualityExpression
{
  override val pSubExpressions = subExpressions
  override val pTerm1: PTerm = term1
  override val pTerm2: PTerm = term2

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PUnfoldingExpression private[silAST]
    (override val predicate: PPredicateExpression,override val expression: PExpression)
    (sourceLocation : SourceLocation)
  extends UnfoldingExpression(predicate, expression)(sourceLocation)
  with PExpression
{
  override val toString = "unfolding " + predicate.toString + " in " + expression.toString

  override val pSubExpressions: Seq[PExpression] = List(predicate, expression)

  override def substitute(s: TypeVariableSubstitution): PUnfoldingExpression =
    new PUnfoldingExpression(predicate.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): PUnfoldingExpression =
    new PUnfoldingExpression(predicate.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): PUnfoldingExpression =
    new PUnfoldingExpression(predicate.substitute(s), expression.substitute(s))(s.sourceLocation(sourceLocation))

  override def equals(other : Any) : Boolean =
    other match{ case e : PUnfoldingExpression => (predicate==e.predicate && expression == e.expression) case _ => false}
  override def hashCode() : Int = predicate.hashCode() + expression.hashCode()

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PUnaryExpression extends UnaryExpression with PExpression {
  override val operand1: PExpression = pOperand1

  protected[expressions] def pOperand1: PExpression

  override def substitute(s: TypeVariableSubstitution): PUnaryExpression =
    new PUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): PUnaryExpression =
    new PUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): PUnaryExpression =
    new PUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
}

object PUnaryExpression {
  def unapply(pube: PUnaryExpression): Option[(UnaryConnective, PExpression)] =
    Some(pube.operator, pube.operand1)
}

private[silAST] final class PUnaryExpressionC private[silAST]
    (override val operator: UnaryConnective,override val operand1: PExpression)
    (sourceLocation : SourceLocation)
  extends UnaryExpression(operator, operand1)(sourceLocation)
  with PUnaryExpression
{
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
    new PBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): PBinaryExpression =
    new PBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): PBinaryExpression =
    new PBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
}

object PBinaryExpression {
  def unapply(pbbe: PBinaryExpression): Option[(BinaryConnective, PExpression, PExpression)] =
    Some(pbbe.operator, pbbe.operand1, pbbe.operand2)
}

private[silAST] final class PBinaryExpressionC private[silAST]
    (override val operator: BinaryConnective,override val operand1: PExpression,override val operand2: PExpression)
    (sourceLocation : SourceLocation)
  extends BinaryExpression(operator, operand1, operand2)(sourceLocation)
  with PBinaryExpression
{
  override val pSubExpressions: Seq[PExpression] = List(operand1, operand2)
  override val pOperand1 = operand1
  override val pOperand2 = operand2
}


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait PDomainPredicateExpression extends DomainPredicateExpression with PExpression
{
  protected[expressions] def pArguments: PTermSequence

  override val arguments: PTermSequence = pArguments

  override def substitute(s: TypeVariableSubstitution): PDomainPredicateExpression =
    new PDomainPredicateExpressionC(predicate.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): PDomainPredicateExpression =
    new PDomainPredicateExpressionC(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): PDomainPredicateExpression =
    new PDomainPredicateExpressionC(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}

private[silAST] final class PDomainPredicateExpressionC
    (override val predicate: DomainPredicate,override val arguments: PTermSequence)
    (override val sourceLocation : SourceLocation)
  extends DomainPredicateExpression(predicate, arguments)(sourceLocation)
  with PDomainPredicateExpression
  with AtomicExpression
{
  override val pArguments = arguments
  override val pSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class PPredicateExpression private[silAST]
    (override val receiver: PTerm,override val predicate: Predicate)
    (sourceLocation : SourceLocation)
  extends PredicateExpression(receiver, predicate)(sourceLocation)
  with PExpression
{
  override val pSubExpressions = Nil

  override def substitute(s: TypeVariableSubstitution): PPredicateExpression =
    new PPredicateExpression(receiver.substitute(s), predicate)(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): PPredicateExpression =
    new PPredicateExpression(receiver.substitute(s), predicate)(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): PPredicateExpression =
    new PPredicateExpression(receiver.substitute(s), predicate)(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//Domain
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DExpression extends Expression
{

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
    new DEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): DEqualityExpression =
    new DEqualityExpressionC(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
}

private[silAST] final class DEqualityExpressionC
    (term1: DTerm,term2: DTerm)
    (sourceLocation : SourceLocation)
  extends EqualityExpression(term1, term2)(sourceLocation)
  with DEqualityExpression
{
  override val dTerm1 = term1
  override val dTerm2 = term2

  override val dSubExpressions = subExpressions
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DUnaryExpression extends UnaryExpression with DExpression
{
  protected[expressions] def dOperand1: DExpression

  override val operand1: DExpression = dOperand1

  override def substitute(s: TypeVariableSubstitution): DUnaryExpression =
    new DUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): DUnaryExpression =
    new DUnaryExpressionC(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
}

object DUnaryExpression {
  def unapply(dube: DUnaryExpression): Option[(UnaryConnective, DExpression)] =
    Some(dube.operator, dube.operand1)
}

private[silAST] final class DUnaryExpressionC private[silAST]
    (override val operator: UnaryConnective,override val operand1: DExpression)
    (sourceLocation : SourceLocation)
  extends UnaryExpression(operator, operand1)(sourceLocation)
  with DUnaryExpression
{
  override val dSubExpressions: Seq[DExpression] = List(operand1)
  override val dOperand1 = operand1
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait DBinaryExpression extends BinaryExpression with DExpression
{
  protected[expressions] def dOperand1: DExpression

  protected[expressions] def dOperand2: DExpression

  override val operand1: DExpression = dOperand1
  override val operand2: DExpression = dOperand2

  override def substitute(s: TypeVariableSubstitution): DBinaryExpression =
    new DBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): DBinaryExpression =
    new DBinaryExpressionC(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
}

object DBinaryExpression {
  def unapply(dbbe: DBinaryExpression): Option[(BinaryConnective, DExpression, DExpression)] =
    Some(dbbe.operator, dbbe.operand1, dbbe.operand2)
}

private[silAST] final class DBinaryExpressionC private[silAST]
    (override val operator: BinaryConnective,override val operand1: DExpression,override val operand2: DExpression)
    (sourceLocation : SourceLocation)
  extends BinaryExpression(operator, operand1, operand2)(sourceLocation)
  with DBinaryExpression
{
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
    new DDomainPredicateExpressionC(sourceLocation, predicate.substitute(s), arguments.substitute(s))
  override def substitute(s: DLogicalVariableSubstitution): DDomainPredicateExpression =
    new DDomainPredicateExpressionC(sourceLocation, predicate, arguments.substitute(s))
}

private[silAST] final class DDomainPredicateExpressionC(
                                                         sourceLocation : SourceLocation,
                                                         override val predicate: DomainPredicate,
                                                         override val arguments: DTermSequence
                                                         )
  extends DomainPredicateExpression(predicate, arguments)(sourceLocation)
  with DDomainPredicateExpression
  with AtomicExpression
{
  override val dArguments = arguments
  override val dSubExpressions = Nil
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class DQuantifierExpression private[silAST]
    (override val quantifier: Quantifier,override val variable: LogicalVariable,override val expression: DExpression)
    (sourceLocation : SourceLocation)
  extends QuantifierExpression(quantifier, variable, expression)(sourceLocation)
  with DExpression
{
  override val subExpressions: Seq[DExpression] = List(expression)
  override val dSubExpressions = subExpressions

  override def substitute(s: TypeVariableSubstitution): DQuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType.substitute(s))(s.sourceLocation(variable.sourceLocation))
    val newS = s + new TypeSubstitutionC(Set(), Set((variable, newVar)),s.sourceLocation, s.newDomain)
    new DQuantifierExpression(quantifier, newVar, expression.substitute(newS))(s.sourceLocation(sourceLocation))
  }
  override def substitute(s: DLogicalVariableSubstitution): DQuantifierExpression = {
    val newVar = new LogicalVariable(variable.name, variable.dataType)(s.sourceLocation(variable.sourceLocation))
    val newS = s + new DLogicalVariableSubstitutionC(Set(), Set((variable, new LogicalVariableTerm(newVar)(newVar.sourceLocation)))/*,s.newDomain*/)
    new DQuantifierExpression(quantifier, newVar, expression.substitute(newS))(s.sourceLocation(sourceLocation))
  }

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
//General/ground
///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
sealed trait GExpression
  extends Expression with DExpression with PExpression
{
  override val subExpressions: Seq[GExpression] = gSubExpressions
  protected[expressions] final override val pSubExpressions = subExpressions
  protected[expressions] final override val dSubExpressions = subExpressions

  protected[expressions] def gSubExpressions: Seq[GExpression]

  def substitute(s: TypeVariableSubstitution): GExpression
  def substitute(s: GLogicalVariableSubstitution): GExpression
}

///////////////////////////////////////////////////////////////////////////
final class GEqualityExpression private[silAST]
    (override val term1: GTerm,override val term2: GTerm)
    (sourceLocation : SourceLocation)
  extends EqualityExpression(term1, term2)(sourceLocation)
  with PEqualityExpression
  with DEqualityExpression
  with GExpression
{
  override val subExpressions: Seq[GExpression] = Nil
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pTerm1 = term1
  protected[expressions] override val pTerm2 = term2
  protected[expressions] override val dTerm1 = term1
  protected[expressions] override val dTerm2 = term2

  override def substitute(s: TypeVariableSubstitution): GEqualityExpression =
    new GEqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): GEqualityExpression =
    new GEqualityExpression(term1.substitute(s), term2.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GUnaryExpression private[silAST]
    (operator: UnaryConnective,override val operand1: GExpression)
    (sourceLocation : SourceLocation)
  extends UnaryExpression(operator, operand1)(sourceLocation)
  with PUnaryExpression
  with DUnaryExpression
  with GExpression
{
  override val subExpressions = List(operand1)
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1

  override def substitute(s: TypeVariableSubstitution): GUnaryExpression =
    new GUnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): GUnaryExpression =
    new GUnaryExpression(operator, operand1.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GBinaryExpression private[silAST]
    (operator: BinaryConnective,override val operand1: GExpression,override val operand2: GExpression)
    (sourceLocation : SourceLocation)
  extends BinaryExpression(operator, operand1, operand2)(sourceLocation)
  with PBinaryExpression
  with DBinaryExpression
  with GExpression
{

  override val subExpressions = List(operand1, operand2)

  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val pOperand1 = operand1
  protected[expressions] override val dOperand1 = operand1
  protected[expressions] override val pOperand2 = operand2
  protected[expressions] override val dOperand2 = operand2

  override def substitute(s: TypeVariableSubstitution): GBinaryExpression =
    new GBinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): GBinaryExpression =
    new GBinaryExpression(operator, operand1.substitute(s), operand2.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final class GDomainPredicateExpression private[silAST]
    (predicate: DomainPredicate,override val arguments: GTermSequence)
    (sourceLocation : SourceLocation)
  extends DomainPredicateExpression(predicate, arguments)(sourceLocation)
  with PDomainPredicateExpression
  with DDomainPredicateExpression
  with GExpression
{
  protected[expressions] override val gSubExpressions = subExpressions
  protected[expressions] override val dArguments = arguments
  protected[expressions] override val pArguments = arguments

  override def substitute(s: TypeVariableSubstitution): GDomainPredicateExpression =
    new GDomainPredicateExpression(predicate.substitute(s), arguments.substitute(s))(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): GDomainPredicateExpression =
    new GDomainPredicateExpression(predicate, arguments.substitute(s))(s.sourceLocation(sourceLocation))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class TrueExpression()(override val sourceLocation : SourceLocation)
  extends Expression
  with GExpression
  with AtomicExpression
{
  override val toString = "true"
  override val subExpressions = List.empty
  override val gSubExpressions = List.empty

  override def substitute(s: TypeVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): TrueExpression = new TrueExpression()(s.sourceLocation(sourceLocation))

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
final case class FalseExpression()(override val sourceLocation : SourceLocation)
  extends Expression
  with GExpression
  with AtomicExpression
{
  override val toString = "false"
  override val subExpressions = List.empty
  override val gSubExpressions = List.empty

  override def substitute(s: TypeVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))

  override def substitute(s: LogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: DLogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: PLogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: GLogicalVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))

  override def substitute(s: ProgramVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))
  override def substitute(s: PProgramVariableSubstitution): FalseExpression = new FalseExpression()(s.sourceLocation(sourceLocation))
}
