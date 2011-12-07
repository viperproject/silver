package silAST.programs.symbols

import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.expressions.util.ExpressionSequence
import silAST.types.DataType
import collection.mutable.ListBuffer
import collection.immutable.List
import silAST.expressions.Expression
import silAST.source.{noLocation, SourceLocation}

final class FunctionSignature private[silAST](
                                               sl: SourceLocation,
                                               pParams: Seq[(SourceLocation, String, DataType)],
                                               val resultType: DataType
                                               ) extends ASTNode(sl) {

  //check no duplicate names
  private[symbols] val pParameters = new ProgramVariableSequence(noLocation, (for (pp <- pParams) yield new ProgramVariable(pp._1, pp._2, pp._3)).toList)
  private[symbols] var pPreconditions = new ListBuffer[Expression]
  private[symbols] var pPostconditions = new ListBuffer[Expression]
  private[symbols] var pMeasure: Option[Term] = None

  val resultVar = new ProgramVariable(noLocation, "result", resultType)

  def arguments: ProgramVariableSequence = new ProgramVariableSequence(noLocation, pParameters)

  def precondition: ExpressionSequence = new ExpressionSequence(noLocation, pPreconditions)

  def postcondition: ExpressionSequence = new ExpressionSequence(noLocation, pPostconditions)

  def terminationMeasure: Term = pMeasure.get

  override def toString =
    arguments.toString + " : " + resultType.toString + "\n" +
      (if (precondition.isEmpty) "" else (for (p <- precondition) yield "requires " + p.toString).mkString("\t", "\t\n", "\n")) +
      (if (postcondition.isEmpty) "" else (for (p <- postcondition) yield "ensures " + p.toString).mkString("\t", "\t\n", "\n")) +
      "\tmeasure " + terminationMeasure.toString + "\n"

  override def subNodes = List(arguments, resultType) ++ precondition.toList ++ postcondition.toList ++ List(terminationMeasure)
}