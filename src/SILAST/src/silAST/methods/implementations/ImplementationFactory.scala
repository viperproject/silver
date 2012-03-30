package silAST.methods.implementations

import silAST.programs.NodeFactory
import silAST.expressions.ExpressionFactory
import silAST.programs.symbols.{Field, ProgramVariable}
import collection.Set
import silAST.source.SourceLocation
import silAST.methods.{ScopeFactory, MethodFactory}
import silAST.types.DataType

//TODO: Should implementations have names/ids?

class ImplementationFactory private[silAST]
  (
    private[silAST] val methodFactory: MethodFactory
  )(sourceLocation: SourceLocation)
  extends NodeFactory
  with ExpressionFactory
  with ScopeFactory
{
  def compile(): Implementation = {
    implementation.pBody = cfgFactory.compile()

    implementation
  }


  /////////////////////////////////////////////////////////////////////////////////////
  def addProgramVariable(name: String, dataType: DataType)(sourceLocation: SourceLocation) = {
    require(programVariables.forall(_.name != name))
    require(dataTypes contains dataType)

    val result = new ProgramVariable(name, dataType)(sourceLocation)
    implementation.pLocals.append(result)
    result
  }

  /////////////////////////////////////////////////////////////////////////////////////
  private[silAST] val implementation = new Implementation(methodFactory.method, this)(sourceLocation)
  /////////////////////////////////////////////////////////////////////////////////////
  val cfgFactory = new CFGFactory(implementation,implementation)(sourceLocation)

  /////////////////////////////////////////////////////////////////////////////////////
//  override val scope = implementation
  override val programFactory = methodFactory.programFactory

  /////////////////////////////////////////////////////////////////////////////////////
  override val parentFactory = Some(methodFactory)

  def localVariables : Set[ProgramVariable] = implementation.pLocals.toSet[ProgramVariable];
//  val fields: Set[Field] = methodFactory.fields

  private[silAST] def parameters = methodFactory.parameters
  private[silAST] def results = methodFactory.results

  override def functions = methodFactory.functions
  override def programVariables = methodFactory.programVariables union localVariables
  override def dataTypes = methodFactory.dataTypes union pDataTypes

  override def predicates = methodFactory.predicates
  override def domainFunctions = methodFactory.domainFunctions
  override def domainPredicates = methodFactory.domainPredicates
           protected[silAST] override def domainFactories = methodFactory.domainFactories


  private[silAST] val cfg = implementation.body

  //  cfg.initialNode.pFactory = cfg.

  override def typeVariables = Set()
}