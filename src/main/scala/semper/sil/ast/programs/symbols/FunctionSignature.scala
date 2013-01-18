package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import semper.sil.ast.expressions.terms.Term
import semper.sil.ast.expressions.util.ExpressionSequence
import semper.sil.ast.types.{TypeVariable, DataType}
import collection.mutable.ListBuffer
import semper.sil.ast.expressions.Expression
import semper.sil.ast.source.{NoLocation, SourceLocation}

final class FunctionSignature private[sil](
                                            paParameters: Seq[(SourceLocation, String, DataType)],
                                            resultType: DataType
                                            )(val sourceLocation: SourceLocation, val comment: List[String])
  extends ASTNode {

  //Check no duplicate names
  require(paParameters.forall(_._2 != "result"))
  require(paParameters.forall((x) => paParameters.find(x._2 == _._2) == Some(x)))

  private[symbols] val pParameters = new ProgramVariableSequence((for (pp <- paParameters) yield new ProgramVariable(pp._2, pp._3)(pp._1, Nil)).toList)(NoLocation, Nil)

  private[symbols] var pPreconditions = new ListBuffer[Expression]
  private[symbols] var pPostconditions = new ListBuffer[Expression]
  private[symbols] var pMeasure: Option[Term] = None

  val result = new ProgramVariable("result", resultType)(NoLocation, Nil)

  lazy val freeTypeVariables: Set[TypeVariable] =
    pParameters.foldLeft(Set[TypeVariable]())(_ union _.dataType.freeTypeVariables) union
      result.dataType.freeTypeVariables union
      pPreconditions.foldLeft(Set[TypeVariable]())(_ union _.freeTypeVariables) union
      pPostconditions.foldLeft(Set[TypeVariable]())(_ union _.freeTypeVariables) union
      (
        terminationMeasure match {
          case Some(t) => t.freeTypeVariables
          case _ => Set[TypeVariable]()
        }
        )

  def parameters: ProgramVariableSequence = new ProgramVariableSequence(pParameters)(NoLocation, Nil)

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