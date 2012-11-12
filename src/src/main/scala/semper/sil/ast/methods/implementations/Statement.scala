package semper.sil.ast.methods.implementations

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.util.PTermSequence
import semper.sil.ast.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import semper.sil.ast.methods.Method
import scala.Some
import semper.sil.ast.expressions.terms.{Term, PredicateLocation, PTerm}
import semper.sil.ast.types.{permissionType, DataType}
import semper.sil.ast.expressions.{PredicatePermissionExpression, Expression}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
sealed abstract class Statement private [sil] extends ASTNode {
  override def toString: String

  def readVariables: Set[ProgramVariable]

  def writtenVariables: Set[ProgramVariable]
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class AssignmentStatement private [sil](
      target: ProgramVariable,
      source: PTerm
      )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement {
  override def toString: String = target.name + ":=" + source.toString

  override val readVariables = source.programVariables.toSet
  override val writtenVariables = Set(target)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
case class FieldAssignmentStatement private [sil](
     target: ProgramVariable,
     field: Field,
     source: PTerm
     )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement {
  override def toString: String = target.name + "." + field.name + " := " + source.toString

  override val readVariables = source.programVariables.toSet union Set(target)
  override val writtenVariables = Set[ProgramVariable]()
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
case class NewStatement private [sil](
         target: ProgramVariable,
         dataType: DataType
         )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement {
  override def toString: String = target.name + ":= new " + dataType.toString

  override val readVariables = Set[ProgramVariable]()
  override val writtenVariables = Set(target)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//TODO:check signature
final case class CallStatement private [sil]
(
  targets: ProgramVariableSequence,
  method: Method,
  arguments: PTermSequence
  )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement {
  def receiver = arguments.head

  override def toString: String = targets.toString + " := " + arguments.head.toString + "." + method.name + arguments.tail.toString

  override val readVariables = (for (a <- arguments) yield a.programVariables).flatten.toSet[ProgramVariable]
  override val writtenVariables = targets.toSet
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class InhaleStatement private [sil](
      expression: Expression
      )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement {
  override def toString: String = "inhale " + expression.toString

  override val readVariables = expression.programVariables
  override val writtenVariables = Set[ProgramVariable]()
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class ExhaleStatement private [sil](
        expression: Expression,
        message : Option[String]
        )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement {

  override def toString: String = message match {
    case Some(m) => "exhale " + expression + "  (\"" + m + "\")"
    case None => "exhale " + expression
  }

  override val readVariables = expression.programVariables
  override val writtenVariables = Set[ProgramVariable]()
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//TODO:FoldStatement/UnfoldStatement arrays?
final case class FoldStatement private [sil](
      location: PredicateLocation,
      permission : Term
      )(override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement
{
  require(permission.dataType==permissionType)

  override def toString: String = "fold " + location.toString + " by " + permission.toString

  override val readVariables = location.programVariables
  override val writtenVariables = Set[ProgramVariable]()
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class UnfoldStatement private [sil]
    (permissionExpression : PredicatePermissionExpression)
    (override val sourceLocation: SourceLocation,val comment:List[String])
  extends Statement
{
  override def toString: String = "unfold " + permissionExpression.toString

  override val readVariables = permissionExpression.programVariables
  override val writtenVariables = collection.immutable.Set[ProgramVariable]()
}
