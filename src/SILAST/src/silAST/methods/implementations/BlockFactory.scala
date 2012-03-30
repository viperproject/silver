package silAST.methods.implementations

import silAST.source.SourceLocation
import collection.Set
import collection.mutable.HashSet
import silAST.methods.Scope
import silAST.programs.NodeFactory
import silAST.expressions.{PExpression, ExpressionFactory}
import silAST.programs.symbols.{ProgramVariable, ProgramVariableSequence, Field}


abstract class BlockFactory private[silAST]
  (
    val scope: Scope,

    val name: String
  ) (val sourceLocation: SourceLocation)
  extends NodeFactory
//  with ExpressionFactory
{
  type B <: Block

  //////////////////////////////////////////////////////////////////
  protected def compile(): B = {
    block
  }

  //////////////////////////////////////////////////////////////////
  def setBranch(condition : PExpression, trueTarget : BlockFactory, falseTarget : BlockFactory)(sl : SourceLocation)
  {
    require (block.pControlStatement == None)
    require(trueTarget.block.cfg == block.cfg)
    require(falseTarget.block.cfg == block.cfg)
    block.setControlStatement(new Branch(block,trueTarget.block,falseTarget.block,condition)(sl))
  }

  //////////////////////////////////////////////////////////////////
  def setGoto(target : BlockFactory)(sl : SourceLocation)
  {
    require (block.pControlStatement == None)
    require(target.block.cfg == block.cfg)
    block.setControlStatement(new Goto(block,target.block)(sl))
  }

  //////////////////////////////////////////////////////////////////
  def setHalt()(sl : SourceLocation)
  {
    require (block.pControlStatement == None)
    block.setControlStatement(new Halt()(sl))
  }

  //////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////
//  val parentFactory = Some(scope.factory)

//  override def fields: Set[Field] = scope.factory.fields

//  override def dataTypes = scope.factory.dataTypes
//  override def programVariables = scope.programVariables
//  override def predicates = scope.factory.predicates
//  override def functions  = scope.factory.functions
//  override def domainFunctions  = scope.factory.domainFunctions
  //override def domainPredicates = scope.factory.domainPredicates
//  override def typeVariables  = scope.factory.typeVariables
//  override protected[silAST] def domainFactories = scope.factory.domainFactories

//  def localVariables = block.localVariables

  //scopedVariables;

//  def results = implementationFactory.results

//  private def parameters = implementationFactory.parameters

//  override def programVariables: Set[ProgramVariable] = scope.
//    localVariables union parameters.toSet[ProgramVariable]

  //  override def functions = implementationFactory.functions

//  override val programVariableSequences = new HashSet[ProgramVariableSequence]

//  override def dataTypes = implementationFactory.dataTypes union pDataTypes

//  override def typeVariables = Set()

  private[silAST] val block: B
}