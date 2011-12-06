package silAST.methods.implementations

import silAST.methods.MethodFactory
import silAST.programs.NodeFactory
import silAST.expressions.ExpressionFactory
import silAST.source.SourceLocation
import silAST.types.DataType
import silAST.programs.symbols.{Field, ProgramVariable}
import collection.Set
import collection.mutable._

//TODO: Should implementations have names/ids?

class ImplementationFactory private[silAST](
    private[silAST] val methodFactory : MethodFactory,
    sl : SourceLocation
    )
  extends NodeFactory with ExpressionFactory
{
  def compile() : Implementation = {
    require (startNode!=None)
    require (endNode!=None)
    for (bbf <- basicBlocks) bbf.compile()

    val cfg = new ControlFlowGraph(sl,for (bbf <- basicBlocks) yield bbf.basicBlock,startNode.basicBlock,endNode.basicBlock)
//    new Implementation(sl,methodFactory.method,localVariables.toSeq,cfg)
    null
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addLocalVariable(sl : SourceLocation, name : String,  dataType : DataType) = {
    require (methodFactory.programVariables.forall(_.name != name))
    require (localVariables.forall(_.name != name))
    require (dataTypes.contains(dataType))
    val result = new ProgramVariable(sl,name,dataType)
    localVariables.append(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addFirstBasicBlock(sl : SourceLocation, name : String) : BasicBlockFactory = {
    require (startNode == None)
    val result = addBasicBlock(sl,name)
    startNode = Some(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addLastBasicBlock(sl : SourceLocation, name : String) : BasicBlockFactory = {
    require (endNode == None)
    val result = addBasicBlock(sl,name)
    endNode = Some(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addBasicBlock(sl : SourceLocation, name : String) : BasicBlockFactory = {
    require(!basicBlocks.contains(name))
    basicBlocks.getOrElseUpdate(name,new BasicBlockFactory(this,sl,name))
  }

  /////////////////////////////////////////////////////////////////////////////////////
  val fields : Set[Field] = methodFactory.fields

//  private[silAST] def methodFactories = methodFactory.methodFactories

  private[silAST] def parameters = methodFactory.parameters
  private[silAST] def results = methodFactory.results
  val localVariables = new ListBuffer[ProgramVariable]
  val basicBlocks = new HashMap[String,BasicBlockFactory]

  private[silAST] def methodFactories = methodFactory.methodFactories

  override val nullFunction = methodFactory.nullFunction
  override def functions = methodFactory.functions
  override def programVariables = parameters.toSet union results.toSet union localVariables.toSet[ProgramVariable]
  override protected[silAST] def predicates = methodFactory.predicates
  override protected[silAST] def domainFunctions = methodFactory.domainFunctions

  override def trueExpression = methodFactory.trueExpression
  override def falseExpression = methodFactory.falseExpression

  protected[silAST] override def dataTypes = methodFactory.dataTypes union pDataTypes
  protected[silAST] override def domainFactories = methodFactory.domainFactories

  var startNode : Option[BasicBlockFactory] = None
  var   endNode : Option[BasicBlockFactory] = None
}