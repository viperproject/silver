package silAST.methods

import implementations.ImplementationFactory
import silAST.programs.{NodeFactory, ProgramFactory}
import collection.mutable.{HashSet, ListBuffer}
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.ExpressionSequence
import silAST.source.{noLocation, SourceLocation}
import silAST.types.{ReferenceDataType, DataType}
import silAST.expressions.{FalseExpression, TrueExpression, Expression, ExpressionFactory}
import silAST.domains.Domain

class MethodFactory(
                     val programFactory: ProgramFactory,
                     val sl : SourceLocation,
                     val name: String
                     ) extends NodeFactory with ExpressionFactory
{
  def compile() : Method =
  {
    if (!signatureDefined)
      finalizeSignature()
    for (i <- implementations) i.compile()

    method
  }

  def addParameter(sl : SourceLocation, name : String, dataType : DataType  ) = {
    require(!signatureDefined)
    require (programVariables.forall(_.name != name))
    val result = new ProgramVariable(sl, name,dataType)
    parametersGenerator += result
//    programVariables += result
    result
  }

  def addResult(sl : SourceLocation, name : String, dataType : DataType  ) = {
    require(!signatureDefined)
    require (programVariables.forall(_.name != name))
    val result = new ProgramVariable(sl, name,dataType)
    resultsGenerator += result
//    programVariables += result
    result
  }

  def addPrecondition(sl : SourceLocation, e : Expression ) = {
    require(!signatureDefined)
    preconditions += e
  }

  def addPostcondition(sl : SourceLocation, e : Expression ) = {
    require(!signatureDefined)
    postconditions += e
  }

  def finalizeSignature() {
    require (!signatureDefined)

    pParameters = Some(new ProgramVariableSequence(sl,parametersGenerator))
    pResults = Some(new ProgramVariableSequence(sl,resultsGenerator))
    val preconditions = new ExpressionSequence(sl,this.preconditions) //TODO:more accurate locations
    val postconditions = new ExpressionSequence(sl,this.postconditions) //TODO:more accurate locations
    val signature = new MethodSignature(sl,pParameters.get,pResults.get,preconditions,postconditions)
    pMethod = Some(new Method(sl,name,signature))
    signatureDefined = true

  }

  def makeImplementation(sl:SourceLocation) = {
    if (!signatureDefined) finalizeSignature()
    val result = new ImplementationFactory(this,sl)
    implementations += result
    result
  }


  //////////////////////////////////////////////////////////////////////////////////////
  private var pMethod : Option[Method] = None
  def method : Method = if (pMethod.isDefined) pMethod.get else throw new Exception
  val fields : Set[Field] = programFactory.fields.toSet

  var pParameters : Option[ProgramVariableSequence] = None
  var pResults : Option[ProgramVariableSequence] = None
  def parameters : ProgramVariableSequence = {
    require (signatureDefined)
    pParameters.get
  }
  def results : ProgramVariableSequence = {
    require (signatureDefined)
    pResults.get
  }
  private val parametersGenerator = new ListBuffer[ProgramVariable]
  private val resultsGenerator = new ListBuffer[ProgramVariable]
  private val preconditions = new ListBuffer[Expression]
  private val postconditions = new ListBuffer[Expression]
  private var signatureDefined = false
  private val implementations = new HashSet[ImplementationFactory]
  private[silAST] def methodFactories = programFactory.methodFactories.values.toSet

  override val nullFunction = programFactory.nullFunction

  override def programVariables = parametersGenerator.toSet[ProgramVariable] union resultsGenerator.toSet[ProgramVariable]
  override def functions = programFactory.functions.toSet
  override protected[silAST] val predicates = programFactory.predicates
  override protected[silAST] def domainFunctions = programFactory.domainFunctions

  val thisVar = addParameter(noLocation,"this",ReferenceDataType.referenceType)

  override def trueExpression = programFactory.trueExpression
  override def falseExpression = programFactory.falseExpression

  override def dataTypes = programFactory.dataTypes union pDataTypes
  override def domainFactories = programFactory.domainFactories
}