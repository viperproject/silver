package silAST.methods.implementations

import silAST.source.SourceLocation
import silAST.methods.Scope
import silAST.programs.NodeFactory
import silAST.expressions.{PExpression, ExpressionFactory}


abstract class BlockFactory private[silAST]
(
  val scope: Scope,
  val name: String
  )(val sourceLocation: SourceLocation,val comment:List[String])
  extends NodeFactory
  with ExpressionFactory {
  type B <: Block

  //////////////////////////////////////////////////////////////////
  protected def compile(): B = {
    block
  }

  //////////////////////////////////////////////////////////////////
  def setBranch(condition: PExpression, trueTarget: BlockFactory, falseTarget: BlockFactory,sl: SourceLocation,comment:List[String] = Nil)
  {
    require(block.pControlStatement == None)
    require(trueTarget.block.cfg == block.cfg)
    require(falseTarget.block.cfg == block.cfg)
    block.setControlStatement(new Branch(block, trueTarget.block, falseTarget.block, condition)(sl,comment))
  }

  //////////////////////////////////////////////////////////////////
  def setGoto(target: BlockFactory,sl: SourceLocation,comment : List[String] = Nil) {
    require(block.pControlStatement == None)
    require(target.block.cfg == block.cfg)
    block.setControlStatement(new Goto(block, target.block)(sl,comment))
  }

  //////////////////////////////////////////////////////////////////
  def setHalt(sl: SourceLocation,comment:List[String] = Nil) {
    require(block.pControlStatement == None)
    block.setControlStatement(new Halt()(sl,comment))
  }

  private[silAST] val block: B
}