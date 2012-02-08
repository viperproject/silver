package silAST.methods.implementations

import silAST.methods.MethodFactory
import silAST.programs.NodeFactory
import silAST.expressions.ExpressionFactory
import silAST.types.DataType
import silAST.programs.symbols.{Field, ProgramVariable}
import collection.Set
import collection.mutable._
import silAST.source.SourceLocation
import silAST.programs.symbols.SymbolFactory
import silAST.programs.ScopeFactory

//TODO: Should implementations have names/ids?

class ImplementationFactory private[silAST](
                                             private[silAST] val methodFactory: MethodFactory,
                                             sl: SourceLocation
                                             )
  extends NodeFactory with ExpressionFactory with ScopeFactory
{
  def compile(): Implementation = {
    require(startNode != None)
    require(endNode != None)
    for (bbf <- basicBlocks) bbf.compile()

    //    val cfg = new ControlFlowGraph(sl,for (bbf <- basicBlocks) yield bbf.basicBlock,startNode.basicBlock,endNode.basicBlock)
    //    new Implementation(sl,methodFactory.method,localVariables.toSeq,cfg)
    implementation
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addLocalVariable(sl: SourceLocation, name: String, dataType: DataType) = {
    require(methodFactory.programVariables.forall(_.name != name))
    require(localVariables.forall(_.name != name))
    require(dataTypes contains dataType)

    val result = new ProgramVariable(sl, name, dataType)
    localVariables.append(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addFirstBasicBlock(sl: SourceLocation, name: String): BasicBlockFactory = {
    require(startNode == None)
    val result = addBasicBlock(sl, name)
    startNode = Some(result)
    cfg.setStartNode(result.basicBlock)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addLastBasicBlock(sl: SourceLocation, name: String): BasicBlockFactory = {
    require(endNode == None)
    val result = addBasicBlock(sl, name)
    endNode = Some(result)
    cfg.setEndNode(result.basicBlock)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addBasicBlock(sl: SourceLocation, name: String): BasicBlockFactory = {
    require(basicBlocks.forall(_.name != name))
    val result = new BasicBlockFactory(this, sl, name)
    basicBlocks += result
    result.basicBlock.cfg = cfg
    cfg.addNode(result.basicBlock)
    result
  }

 
  override val parentFactory = Some(methodFactory)
  
  /////////////////////////////////////////////////////////////////////////////////////
  private[silAST] val implementation = new Implementation(sl, methodFactory.method,this)
  /////////////////////////////////////////////////////////////////////////////////////
  val fields: Set[Field] = methodFactory.fields

  private[silAST] def parameters = methodFactory.parameters

  private[silAST] def results = methodFactory.results

  def localVariables = implementation.pLocals; // ListBuffer[ProgramVariable]
  val basicBlocks = new HashSet[BasicBlockFactory]

//  private[silAST] def methodFactories = methodFactory.methodFactories

  override val nullFunction = methodFactory.nullFunction

  override def functions = methodFactory.functions

  override def programVariables = parameters.toSet union results.toSet union localVariables.toSet[ProgramVariable]

  override protected[silAST] def predicates = methodFactory.predicates

  override protected[silAST] def domainFunctions = methodFactory.domainFunctions

  override protected[silAST] def domainPredicates = methodFactory.domainPredicates

  protected[silAST] override def dataTypes = methodFactory.dataTypes union pDataTypes

  protected[silAST] override def domainFactories = methodFactory.domainFactories

  var startNode: Option[BasicBlockFactory] = None
  var endNode: Option[BasicBlockFactory] = None

  private[silAST] val cfg = implementation.body

//  cfg.initialNode.pFactory = cfg.

  override def typeVariables = Set()
}