package semper.sil.ast.methods.implementations

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.methods.Scope
import semper.sil.ast.programs.NodeFactory
import semper.sil.ast.expressions.{Expression, ExpressionFactory}


abstract class BlockFactory private[sil]
(
  val scope: Scope,
  val name: String
  )(val sourceLocation: SourceLocation, val comment: List[String])
  extends NodeFactory
  with ExpressionFactory {
  type B <: Block

  //////////////////////////////////////////////////////////////////
  protected def compile(): B = {
    block
  }

  //////////////////////////////////////////////////////////////////
  def setBranch(condition: Expression, trueTarget: BlockFactory, falseTarget: BlockFactory, sl: SourceLocation, comment: List[String] = Nil) {
    require(block.pControlStatement == None)
    require(trueTarget.block.cfg == block.cfg)
    require(falseTarget.block.cfg == block.cfg)
    block.setControlStatement(new Branch(block, trueTarget.block, falseTarget.block, condition)(sl, comment))
  }

  //////////////////////////////////////////////////////////////////
  def setGoto(target: BlockFactory, sl: SourceLocation, comment: List[String] = Nil) {
    require(block.pControlStatement == None)
    require(target.block.cfg == block.cfg)
    block.setControlStatement(new Goto(block, target.block)(sl, comment))
  }

  //////////////////////////////////////////////////////////////////
  def setHalt(sl: SourceLocation, comment: List[String] = Nil) {
    require(block.pControlStatement == None)
    block.setControlStatement(new Halt()(sl, comment))
  }

  private[sil] val block: B
}