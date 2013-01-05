package semper.sil.ast.methods.implementations

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.expressions.{PExpression, Expression}
import semper.sil.ast.methods.{ScopeFactory, Scope}
import semper.sil.ast.types.{DataType, TypeVariable}
import semper.sil.ast.programs.symbols.ProgramVariable

class LoopBlockFactory(
                        cfg: ControlFlowGraph,
                        val parentScope: Scope,
                        implementation: Implementation,
                        name: String,
                        condition: PExpression
                        )
                      (override val sourceLocation: SourceLocation, override val comment: List[String])
  extends BlockFactory(parentScope, name)(sourceLocation, comment)
  with ScopeFactory {
  type B = LoopBlock

  override val programFactory = parentScope.factory.programFactory
  override val parentFactory = Some(parentScope.factory)

  override def inputProgramVariables = implementation.factory.inputProgramVariables

  override def outputProgramVariables = implementation.factory.outputProgramVariables

  override def compile(): LoopBlock = {
    require(block.pInvariant != None)
    bodyFactory.compile()
    block
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def addProgramVariable(name: String, dataType: DataType)(sourceLocation: SourceLocation) = {
    require(programVariables.forall(_.name != name))
    require(dataTypes contains dataType)

    val result = new ProgramVariable(name, dataType)(sourceLocation, Nil)
    scope.pLocals.append(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  def setInvariant(e: Expression) {
    migrate(e)
    require(block.pInvariant == None)
    block.pInvariant = Some(e)
  }

  /////////////////////////////////////////////////////////////////////////////////////
  val block = new LoopBlock(this, cfg, implementation, name, scope, condition)(sourceLocation, comment)
  val bodyFactory = block.bodyFactory
  val typeVariables: Set[TypeVariable] = Set()

  override def programVariables = block.programVariables
}
