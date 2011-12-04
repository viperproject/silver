package silAST.methods.implementations

import silAST.ASTNode
import silAST.expressions.PExpression
import silAST.types.DataType
import silAST.expressions.Expression
import silAST.expressions.PredicateExpression
import silAST.source.SourceLocation
import silAST.expressions.util.PTermSequence
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.methods.Method

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
sealed abstract class Statement private[silAST](
                                                 sl: SourceLocation
                                                 ) extends ASTNode(sl) {
  override def toString: String
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class Assignment private[silAST](
                                             sl: SourceLocation,
                                             target: ProgramVariable,
                                             source: PExpression
                                             )
  extends Statement(sl) {
  override def toString: String = target.name + ":=" + source.toString

  override def subNodes: Seq[ASTNode] = List(target, source)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
case class FieldAssignment private[silAST](
                                            sl: SourceLocation,
                                            target: ProgramVariable,
                                            field: Field,
                                            source: PExpression
                                            )
  extends Statement(sl) {
  override def toString: String = target.name + "." + field.name + " := " + source.toString

  override def subNodes: Seq[ASTNode] = List(target, field, source)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
case class NewStatement private[silAST](
                                         sl: SourceLocation,
                                         target: ProgramVariable,
                                         dataType: DataType
                                         )
  extends Statement(sl) {
  override def toString: String = target.name + ":= new " + dataType.toString

  override def subNodes: Seq[ASTNode] = List(target, dataType)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class CallStatement private[silAST]
(
  sl: SourceLocation,
  targets: ProgramVariableSequence,
  receiver: PExpression,
  method: Method,
  arguments: PTermSequence
  )
  extends Statement(sl) {
  override def toString: String = targets.toString + " := " + receiver.toString + "." + method.name + arguments.toString

  override def subNodes: Seq[ASTNode] = List(targets, receiver, method, arguments)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class Inhale private[silAST](
                                         sl: SourceLocation,
                                         expression: Expression
                                         )
  extends Statement(sl) {
  override def toString: String = "inhale " + expression.toString

  override def subNodes: Seq[ASTNode] = List(expression)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class Exhale private[silAST](
                                         sl: SourceLocation,
                                         expression: Expression
                                         )
  extends Statement(sl) {
  override def toString: String = "exhale " + expression.toString

  override def subNodes: Seq[ASTNode] = List(expression)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//TODO:Fold/Unfold arrays?
final case class Fold private[silAST](
                                       sl: SourceLocation,
                                       predicate: PredicateExpression
                                       )
  extends Statement(sl) {
  override def toString: String = "Fold " + predicate.toString

  override def subNodes: Seq[ASTNode] = List(predicate)
}

//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////
final case class Unfold private[silAST](
                                         sl: SourceLocation,
                                         predicate: PredicateExpression
                                         )
  extends Statement(sl) {
  override def toString: String = "Unfold " + predicate.toString

  override def subNodes: Seq[ASTNode] = List(predicate)
}
