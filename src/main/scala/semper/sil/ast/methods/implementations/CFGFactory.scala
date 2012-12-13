package semper.sil.ast.methods.implementations

import semper.sil.ast.programs.NodeFactory
import collection.mutable.HashSet
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.methods.Scope
import semper.sil.ast.expressions.PExpression
import collection.mutable

final class CFGFactory(
                        implementation: Implementation,
                        val scope: Scope
                        )
                      (sourceLocation: SourceLocation)
  extends NodeFactory {
  /////////////////////////////////////////////////////////////////////////////////////
  def compile(): ControlFlowGraph = {
    require(cfg.pStartNode != null)
    require(cfg.pEndNode != null)
    cfg.compile()

    cfg
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def setStartNode(blockF: BasicBlockFactory) {
    require(blocks contains blockF)
    require(cfg.pStartNode == None)
    cfg.setStartNode(blockF.block)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def setEndNode(blockF: BasicBlockFactory) {
    require(blocks contains blockF)
    require(cfg.pEndNode == None)
    require(blockF.block.pControlStatement != None && blockF.block.successors.size == 0)
    cfg.setEndNode(blockF.block)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addBasicBlock(name: String,sourceLocation: SourceLocation,comment : List[String] = Nil): BasicBlockFactory = {
    require(blocks.forall(_.name != name))
    val result = new BasicBlockFactory(cfg, name)(sourceLocation,comment)
    blocks += result
    cfg.addNode(result.block)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addLoopBlock(name: String, condition: PExpression,sourceLocation: SourceLocation,comment : List[String] = Nil): LoopBlockFactory = {
    require(blocks.forall(_.name != name))
    scope.factory.migrateP(condition)
    val result = new LoopBlockFactory(cfg, scope, implementation, name, condition)(sourceLocation,comment)
    blocks += result
    cfg.addNode(result.block)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////
  val blocks = new mutable.HashSet[BlockFactory]
  var startNode: Option[BasicBlockFactory] = None
  var endNode: Option[BasicBlockFactory] = None
  private [sil] val cfg = new ControlFlowGraph(scope, implementation)(sourceLocation,Nil)


}
