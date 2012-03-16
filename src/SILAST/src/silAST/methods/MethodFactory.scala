package silAST.methods

import implementations.ImplementationFactory
import silAST.programs.{NodeFactory, ProgramFactory}
import collection.mutable.{HashSet, ListBuffer}
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.ExpressionSequence
import silAST.source.{noLocation, SourceLocation}
import silAST.expressions.{Expression, ExpressionFactory}
import silAST.types.{referenceType, DataType}

class MethodFactory(
                     val programFactory: ProgramFactory,
                     val sourceLocation : SourceLocation,
                     val name: String
                     )
  extends NodeFactory
  with ExpressionFactory
  with ScopeFactory
{
//  override def scope = method

  def compile(): Method = {
    if (!signatureDefined)
      finalizeSignature()
    for (i <- implementationFactories) i.compile()

    method
  }

  def addParameter(sourceLocation : SourceLocation, name: String, dataType: DataType) = {
    require(!signatureDefined)
    require(programVariables.forall(_.name != name))
    val result = new ProgramVariable(sourceLocation, name, dataType)
    parametersGenerator += result
    //    programVariables += result
    result
  }

  def addResult(sourceLocation : SourceLocation, name: String, dataType: DataType) = {
    require(!signatureDefined)
    require(programVariables.forall(_.name != name))
    val result = new ProgramVariable(sourceLocation, name, dataType)
    resultsGenerator += result
    //    programVariables += result
    result
  }

  def addPrecondition(sourceLocation : SourceLocation, e: Expression) = {
    require(!signatureDefined)
    preconditions += e
  }

  def addPostcondition(sourceLocation : SourceLocation, e: Expression) = {
    require(!signatureDefined)
    postconditions += e
  }

  def finalizeSignature() {
    require(!signatureDefined)

    pParameters = Some(new ProgramVariableSequence(sourceLocation, parametersGenerator))
    pResults = Some(new ProgramVariableSequence(sourceLocation, resultsGenerator))
    val preconditions = new ExpressionSequence(this.preconditions) //TODO:more accurate locations
    val postconditions = new ExpressionSequence(this.postconditions) //TODO:more accurate locations
    val signature = new MethodSignature(sourceLocation, pParameters.get, pResults.get, preconditions, postconditions)
    pMethod = Some(new Method(sourceLocation, name, signature,this))
//    signatureDefined = true

  }

  def addImplementation(sourceLocation : SourceLocation): ImplementationFactory = {
    if (!signatureDefined) finalizeSignature()
    val result = new ImplementationFactory(this, sourceLocation)
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
  private def signatureDefined = pMethod!=None;
  private val implementationFactories = new HashSet[ImplementationFactory]

//  private[silAST] def methodFactories = programFactory.methodFactories

  override def programVariables = parametersGenerator.toSet[ProgramVariable] union resultsGenerator.toSet[ProgramVariable]

//  protected[silAST] override def functions = programFactory.functions.toSet

//  protected[silAST] override def predicates = programFactory.predicates

//  protected[silAST] override def dataTypes = programFactory.dataTypes union pDataTypes

//  protected[silAST] override def domainFactories = programFactory.domainFactories

//  protected[silAST] override def domainFunctions = programFactory.domainFunctions

//  protected[silAST] override def domainPredicates = programFactory.domainPredicates
  override def typeVariables = Set()
}