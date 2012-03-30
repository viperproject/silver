package silAST.methods.implementations

import silAST.source.SourceLocation
import silAST.expressions.{PExpression, Expression}
import silAST.methods.{ScopeFactory, Scope}
import silAST.types.{DataType, TypeVariable}
import silAST.programs.symbols.ProgramVariable

class LoopBlockFactory(
    cfg : ControlFlowGraph,
    val parentScope:Scope,
    implementation : Implementation,
    name : String,
    condition : PExpression
  )
  (sourceLocation : SourceLocation)
  extends BlockFactory(parentScope,name)(sourceLocation)
  with ScopeFactory
{
  type B = LoopBlock

  override val programFactory = parentScope.factory.programFactory
  override val parentFactory =  Some(parentScope.factory)

  override def compile() : LoopBlock =
  {
    require (block.pInvariant!=None)
    bodyFactory.compile()
    block
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addProgramVariable(name: String, dataType: DataType)(sourceLocation: SourceLocation) = {
    require(programVariables.forall(_.name != name))
    require(dataTypes contains dataType)

    val result = new ProgramVariable(name, dataType)(sourceLocation)
    scope.pLocals.append(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def setInvariant(e:Expression)
  {
    migrate(e)
    require(block.pInvariant==None)
    block.pInvariant = Some(e)
  }
  /////////////////////////////////////////////////////////////////////////////////////
  val block = new LoopBlock(this,cfg,implementation,name,scope,condition)(sourceLocation)
  val bodyFactory = block.bodyFactory
  val typeVariables : Set[TypeVariable] = Set()

  override def programVariables = block.programVariables
}
