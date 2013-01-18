package semper.sil.ast.programs.symbols

import semper.sil.ast.programs.ProgramFactory
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.types.DataType
import semper.sil.ast.expressions.Expression

class FunctionFactory private[sil](
                                    private val programFactory: ProgramFactory,
                                    val name: String,
                                    pParameters: Seq[(SourceLocation, String, DataType)],
                                    resultType: DataType
                                    )(val sourceLocation: SourceLocation, comment: List[String])
  extends SymbolFactory[Function](programFactory) {
  def compile(): Function = {
    require(pFunction.pBody != None)
    require(pFunction.pSignature.terminationMeasure != None)
    pFunction
  }

  def addPrecondition(e: Expression) = {
    require(expressions contains e)
    pFunction.pSignature.pPreconditions += e
  }

  def addPostcondition(e: Expression) = {
    require(expressions contains e)
    pFunction.pSignature.pPostconditions += e
  }

  def setMeasure(t: Expression) {
    require(expressions contains t)
    require(pFunction.pSignature.pMeasure == None)
    pFunction.pSignature.pMeasure = Some(t)
  }

  def setBody(t: Expression) {
    require(pFunction.pBody == None)
    require(expressions contains t)
    pFunction.pBody = Some(t)
  }

  def parameters: ProgramVariableSequence = pFunction.pSignature.pParameters

  protected[sil] override def programVariables = Set(thisVar, resultVar) ++ pFunction.pSignature.pParameters

  protected[sil] override def inputProgramVariables = Set(thisVar) ++ pFunction.pSignature.pParameters

  protected[sil] override def outputProgramVariables = Set(resultVar)

  private[sil] val pFunction = new Function(name, pParameters, resultType)(sourceLocation, this, comment)
  val resultVar = pFunction.pSignature.result

  override def typeVariables = Set()

}