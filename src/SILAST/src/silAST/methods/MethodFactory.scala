package silAST.methods

import implementations.ImplementationFactory
import silAST.programs.{NodeFactory, ProgramFactory}
import collection.mutable.{HashSet, ListBuffer}
import silAST.programs.symbols.{ProgramVariableSequence, ProgramVariable}
import silAST.expressions.util.ExpressionSequence
import silAST.source.SourceLocation
import silAST.expressions.{Expression, ExpressionFactory}
import silAST.types.DataType

class MethodFactory(
                     val programFactory: ProgramFactory,
                     val name: String
                     )(val sourceLocation: SourceLocation)
  extends NodeFactory
  with ExpressionFactory
  with ScopeFactory {
  //  override def scope = method

  def compile(): Method = {
    if (!signatureDefined)
      finalizeSignature()
    for (i <- implementationFactories) i.compile()

    method
  }

  def addParameter(name: String, dataType: DataType)(sourceLocation: SourceLocation) = {
    require(!signatureDefined)
    require(programVariables.forall(_.name != name))
    val result = new ProgramVariable(name, dataType)(sourceLocation)
    parametersGenerator += result
    //    programVariables += result
    result
  }

  def addResult(name: String, dataType: DataType)(sourceLocation: SourceLocation) = {
    require(!signatureDefined)
    require(programVariables.forall(_.name != name))
    val result = new ProgramVariable(name, dataType)(sourceLocation)
    resultsGenerator += result
    //    programVariables += result
    result
  }

  def addPrecondition(e: Expression)(sourceLocation: SourceLocation) = {
    require(!signatureDefined)
    preconditions += e
  }

  def addPostcondition(e: Expression)(sourceLocation: SourceLocation) = {
    require(!signatureDefined)
    postconditions += e
  }

  def finalizeSignature() {
    require(!signatureDefined)

    pParameters = Some(new ProgramVariableSequence(parametersGenerator)(sourceLocation))
    pResults = Some(new ProgramVariableSequence(resultsGenerator)(sourceLocation))
    val preconditions = new ExpressionSequence(this.preconditions) //TODO:more accurate locations
    val postconditions = new ExpressionSequence(this.postconditions) //TODO:more accurate locations
    val signature = new MethodSignature(pParameters.get, pResults.get, preconditions, postconditions)(sourceLocation)
    pMethod = Some(new Method(name, signature, this)(sourceLocation))
    //    signatureDefined = true

  }

  def addImplementation()(sourceLocation: SourceLocation): ImplementationFactory = {
    if (!signatureDefined) finalizeSignature()
    val result = new ImplementationFactory(this)(sourceLocation)
    implementationFactories += result
    method.pImplementations += result.implementation
    result
  }


  //////////////////////////////////////////////////////////////////////////////////////
  private var pMethod: Option[Method] = None

  def method: Method = if (pMethod.isDefined) pMethod.get else throw new Exception

  protected[silAST] override val parentFactory = Some(programFactory)

  //  val fields: Set[Field] = programFactory.fields.toSet

  var pParameters: Option[ProgramVariableSequence] = None
  var pResults: Option[ProgramVariableSequence] = None

  def parameters: ProgramVariableSequence = {
    require(signatureDefined)
    pParameters.get
  }

  def results: ProgramVariableSequence = {
    require(signatureDefined)
    pResults.get
  }

  private val parametersGenerator = new ListBuffer[ProgramVariable]
  private val resultsGenerator = new ListBuffer[ProgramVariable]
  private val preconditions = new ListBuffer[Expression]
  private val postconditions = new ListBuffer[Expression]

  private def signatureDefined = pMethod != None;
  private val implementationFactories = new HashSet[ImplementationFactory]

  //  private[silAST] def methodFactories = programFactory.methodFactories

  override def programVariables = inputProgramVariables union outputProgramVariables

  override def inputProgramVariables = parametersGenerator.toSet[ProgramVariable]

  override def outputProgramVariables = resultsGenerator.toSet[ProgramVariable]

  //  protected[silAST] override def functions = programFactory.functions.toSet

  //  protected[silAST] override def predicates = programFactory.predicates

  //  protected[silAST] override def dataTypes = programFactory.dataTypes union pDataTypes

  //  protected[silAST] override def domainFactories = programFactory.domainFactories

  //  protected[silAST] override def domainFunctions = programFactory.domainFunctions

  //  protected[silAST] override def domainPredicates = programFactory.domainPredicates
  override def typeVariables = Set()
}