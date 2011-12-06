package silAST.methods.implementations

import silAST.methods.MethodFactory
import silAST.programs.NodeFactory
import silAST.expressions.ExpressionFactory
import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.symbols.{Field, ProgramVariable}
import collection.Set
import collection.mutable.{HashSet, HashMap}

//TODO: Should implementations have names/ids?

class ImplementationFactory private[silAST](private[silAST] val methodFactory : MethodFactory)
  extends NodeFactory with ExpressionFactory
{
  /////////////////////////////////////////////////////////////////////////////////////
  def addLocalVariable(sl : SourceLocation, name : String,  dataType : DataType) = {
    require (methodFactory.parametersGenerator.forall(_.name != name))
    require (localVariables.forall(_.name != name))
    require (dataTypes.contains(dataType))
    val result = new ProgramVariable(sl,name,dataType)
    localVariables += result
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addBasicBlock(sl : SourceLocation, name : String) : BasicBlockFactory = {
    require(!basicBlocks.contains(name))
    basicBlocks.getOrElseUpdate(name,new BasicBlockFactory(this,sl,name))
  }

  /////////////////////////////////////////////////////////////////////////////////////
  val fields : Set[Field] = methodFactory.fields

  val methodFactories = methodFactory.methodFactories

  val parameters = methodFactory.parameters
  val localVariables = new HashSet[ProgramVariable]
  val results = methodFactory.results
  val basicBlocks = new HashMap[String,BasicBlockFactory]

  override val nullFunction = methodFactory.nullFunction
  override def functions = methodFactory.functions
  override def programVariables = parameters.toSet union results.toSet union localVariables.toSet
  override protected[silAST] def predicates = methodFactory.predicates
  override protected[silAST] def domainFunctions = methodFactory.domainFunctions
}