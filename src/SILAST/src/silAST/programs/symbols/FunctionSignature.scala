package silAST.programs.symbols

import silAST.ASTNode
import silAST.expressions.terms.Term
import silAST.expressions.util.ExpressionSequence
import silAST.types.DataType
import collection.mutable.ListBuffer
import silAST.expressions.Expression
import silAST.source.{noLocation, SourceLocation}

final class FunctionSignature private[silAST](
         paParameters: Seq[(SourceLocation, String, DataType)],
         resultType: DataType
         )(val sourceLocation: SourceLocation,val comment:List[String])
  extends ASTNode {

  //Check no duplicate names
  require(paParameters.forall(_._2 != "result"))
  require(paParameters.forall((x) => paParameters.find(x._2 == _._2) == Some(x)))

  private[symbols] val pParameters = new ProgramVariableSequence((for (pp <- paParameters) yield new ProgramVariable(pp._2, pp._3)(pp._1,Nil)).toList)(noLocation,Nil)

  private[symbols] var pPreconditions = new ListBuffer[Expression]
  private[symbols] var pPostconditions = new ListBuffer[Expression]
  private[symbols] var pMeasure: Option[Term] = None

  val result = new ProgramVariable("result", resultType)(noLocation,Nil)

  def parameters: ProgramVariableSequence = new ProgramVariableSequence(pParameters)(noLocation,Nil)

  def precondition: ExpressionSequence = new ExpressionSequence(pPreconditions)

  def postcondition: ExpressionSequence = new ExpressionSequence(pPostconditions)

  def terminationMeasure: Option[Term] = pMeasure

  override def toString =
    parameters.toString + " : " + result.toString + "\n" +
      (if (precondition.isEmpty) "" else (for (p <- precondition) yield "requires " + p.toString).mkString("\t", "\t\n", "\n")) +
      (if (postcondition.isEmpty) "" else (for (p <- postcondition) yield "ensures " + p.toString).mkString("\t", "\t\n", "\n")) +
      (terminationMeasure match {
        case Some(m) => "\tmeasure " + m.toString + "\n"
        case _ => ""
      })

  override def equals(other: Any): Boolean = {
    other match {
      case s: FunctionSignature =>
        parameters == s.parameters &&
          precondition == s.precondition &&
          postcondition == s.postcondition &&
          terminationMeasure == s.terminationMeasure
      case _ => false
    }
  }

  override def hashCode(): Int = parameters.hashCode() + precondition.hashCode() + postcondition.hashCode() + terminationMeasure.hashCode()

}