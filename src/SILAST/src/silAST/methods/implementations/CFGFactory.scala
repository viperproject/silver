package silAST.methods.implementations

import silAST.programs.NodeFactory
import collection.mutable.HashSet
import silAST.source.SourceLocation
import silAST.methods.Scope
import silAST.expressions.PExpression

final class CFGFactory(
    implementation : Implementation,
    val scope : Scope
  )
  (sourceLocation : SourceLocation)
  extends NodeFactory
{
  /////////////////////////////////////////////////////////////////////////////////////
  def compile() : ControlFlowGraph =
  {
    require(cfg.pStartNode!=null)
    require(cfg.pEndNode!=null)
    cfg.compile()

    cfg
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def setStartNode(blockF : BasicBlockFactory)
  {
    require(blocks contains blockF)
    require(cfg.pStartNode == None)
    cfg.setStartNode(blockF.block)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def setEndNode(blockF : BasicBlockFactory)
  {
    require(blocks contains blockF)
    require(cfg.pEndNode == None)
    require(blockF.block.pControlStatement!=None && blockF.block.successors.size==0)
    cfg.setEndNode(blockF.block)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addBasicBlock(name: String)(sourceLocation: SourceLocation): BasicBlockFactory = {
    require(blocks.forall(_.name != name))
    val result = new BasicBlockFactory(cfg, name)(sourceLocation)
    blocks += result
    cfg.addNode(result.block)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addLoopBlock(name: String, condition : PExpression)(sourceLocation: SourceLocation): LoopBlockFactory = {
    require(blocks.forall(_.name != name))
    scope.factory.migrateP(condition)
    val result = new LoopBlockFactory(cfg,scope,implementation,name,condition)(sourceLocation)
    blocks += result
    cfg.addNode(result.block)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////
  val blocks = new HashSet[BlockFactory]
  var startNode: Option[BasicBlockFactory] = None
  var endNode: Option[BasicBlockFactory] = None
  private[silAST] val cfg = new ControlFlowGraph(scope, implementation)(sourceLocation)


}
