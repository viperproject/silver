package semper.sil.ast.methods.implementations

import semper.sil.ast.programs.NodeFactory
import semper.sil.ast.expressions.ExpressionFactory
import semper.sil.ast.programs.symbols.ProgramVariable
import collection.Set
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.methods.{ScopeFactory, MethodFactory}
import semper.sil.ast.types.DataType

//TODO: Should implementations have names/ids?

class ImplementationFactory private[sil]
(
  private[sil] val methodFactory: MethodFactory
  )(sourceLocation: SourceLocation, comment: List[String])
  extends NodeFactory
  with ExpressionFactory
  with ScopeFactory {
  def compile(): Implementation = {
    implementation.pBody = cfgFactory.compile()

    implementation
  }


  /////////////////////////////////////////////////////////////////////////////////////
  def addProgramVariable(name: String, dataType: DataType)(sourceLocation: SourceLocation) = {
    require(programVariables.forall(_.name != name))
    require(dataTypes contains dataType)

    val result = new ProgramVariable(name, dataType)(sourceLocation, Nil)
    implementation.pLocals.append(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  private[sil] val implementation = new Implementation(methodFactory.method, this)(sourceLocation, comment)
  /////////////////////////////////////////////////////////////////////////////////////
  val cfgFactory = new CFGFactory(implementation, implementation)(sourceLocation)

  /////////////////////////////////////////////////////////////////////////////////////
  //  override val scope = implementation
  override val programFactory = methodFactory.programFactory

  /////////////////////////////////////////////////////////////////////////////////////
  override val parentFactory = Some(methodFactory)

  def localVariables: Set[ProgramVariable] = implementation.pLocals.toSet[ProgramVariable]

  //  val fields: Set[Field] = methodFactory.fields

  private[sil] def parameters = methodFactory.parameters

  private[sil] def results = methodFactory.results

  override def functions = methodFactory.functions

  override def programVariables = methodFactory.programVariables union localVariables

  override val inputProgramVariables = methodFactory.inputProgramVariables
  override val outputProgramVariables = methodFactory.outputProgramVariables

  override def dataTypes = methodFactory.dataTypes union pDataTypes

  override def predicates = methodFactory.predicates

  override def domainFunctions = methodFactory.domainFunctions

  override def domainPredicates = methodFactory.domainPredicates

  protected[sil] override def domainFactories = methodFactory.domainFactories


  private[sil] val cfg = implementation.body

  //  cfg.initialNode.pFactory = cfg.

  override def typeVariables = Set()
}