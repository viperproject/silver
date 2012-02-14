package silAST.programs.symbols

import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.expressions.util.ExpressionSequence
import silAST.types.DataType
import collection.mutable.ListBuffer
import silAST.expressions.Expression
import silAST.source.{noLocation, SourceLocation}

final class FunctionSignature private[silAST](
                                               val sourceLocation : SourceLocation,
                                               paParameters : Seq[(SourceLocation, String, DataType)],
                                               resultType : DataType
                                               ) extends ASTNode{

  //Check no duplicate names
  require (paParameters.forall(_._2 != "result"))
  require (paParameters.forall((x) => paParameters.find(x._2 == _._2) ==Some(x)))

  private[symbols] val pParameters = new ProgramVariableSequence(noLocation, (for (pp <- paParameters) yield new ProgramVariable(pp._1, pp._2, pp._3)).toList)

  private[symbols] var pPreconditions = new ListBuffer[Expression]
  private[symbols] var pPostconditions = new ListBuffer[Expression]
  private[symbols] var pMeasure: Option[Term] = None

  val result = new ProgramVariable(noLocation, "result", resultType)

  def parameters  : ProgramVariableSequence = new ProgramVariableSequence(noLocation, pParameters)

  def precondition: ExpressionSequence = new ExpressionSequence(pPreconditions)

  def postcondition: ExpressionSequence = new ExpressionSequence(pPostconditions)

  def terminationMeasure: Option[Term] = pMeasure

  override def toString =
    parameters.toString + " : " + result.toString + "\n" +
      (if (precondition.isEmpty) "" else (for (p <- precondition) yield "requires " + p.toString).mkString("\t", "\t\n", "\n")) +
      (if (postcondition.isEmpty) "" else (for (p <- postcondition) yield "ensures " + p.toString).mkString("\t", "\t\n", "\n")) +
      (terminationMeasure match {case Some(m) => "\tmeasure " + m.toString + "\n" case _ => "" })

}