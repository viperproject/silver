package silAST.methods

import implementations.ImplementationFactory
import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.{NodeFactory, ProgramFactory}
import silAST.expressions.{Expression, ExpressionFactory}
import collection.mutable.{HashSet, ListBuffer}
import silAST.programs.symbols.{ProgramVariableSequence, Field, ProgramVariable}
import silAST.expressions.util.ExpressionSequence

class MethodFactory(
                     val programFactory: ProgramFactory,
                     val sl : SourceLocation,
                     val name: String
                     ) extends NodeFactory with ExpressionFactory
{
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
    val signature = new MethodSignature(sl,parameters,results,preconditions,postconditions)
    pMethod = Some(new Method(sl,name,signature))
    signatureDefined = true

  }

  def makeImplementation = {
    if (!signatureDefined) finalizeSignature()
    val result = new ImplementationFactory(this)
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
  val parametersGenerator = new ListBuffer[ProgramVariable]
  val resultsGenerator = new ListBuffer[ProgramVariable]
  val preconditions = new ListBuffer[Expression]
  val postconditions = new ListBuffer[Expression]
  var signatureDefined = false
  val implementations = new HashSet[ImplementationFactory]
  val methodFactories = programFactory.methodFactories.values.toSet

  override def programVariables = parametersGenerator.toSet[ProgramVariable] union resultsGenerator.toSet[ProgramVariable]
  override def functions = programFactory.functions.toSet
  override protected[silAST] val predicates = programFactory.predicates
}