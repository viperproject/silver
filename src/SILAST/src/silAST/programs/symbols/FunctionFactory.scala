package silAST.programs.symbols

import silAST.programs.ProgramFactory
import silAST.source.SourceLocation
import silAST.expressions.terms.Term
import silAST.types.DataType
import silAST.expressions.Expression
import silAST.expressions.terms.permission.PermissionVariable

class FunctionFactory private[silAST](
                                       private val programFactory: ProgramFactory,
                                       val sl: SourceLocation,
                                       val name: String,
                                       pParameters: Seq[(SourceLocation, String, DataType)],
                                       resultType : DataType
                                       ) extends SymbolFactory[Function](programFactory) {
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

  def setMeasure(t: Term) {
    require(terms contains t)
    require(pFunction.pSignature.pMeasure == None)
    pFunction.pSignature.pMeasure = Some(t)
  }

  def setBody(t: Term) {
    require(pFunction.pBody == None)
    require(terms contains t)
    pFunction.pBody = Some(t)
  }

  def parameters: ProgramVariableSequence = pFunction.pSignature.pParameters

  protected[silAST] override def programVariables = Set(thisVar, resultVar) ++ pFunction.pSignature.pParameters

  private[silAST] val pFunction = new Function(sl, name,pParameters, resultType)
  val resultVar = pFunction.pSignature.result

  override val permissionVariables : Set[PermissionVariable] = Set() //TODO:fill in/remove
//  val permissionParameters = for (p <- pPermissionParams) yield new PermissionVariable(p._1,p._2)
//  val permissionReturnValues =
}