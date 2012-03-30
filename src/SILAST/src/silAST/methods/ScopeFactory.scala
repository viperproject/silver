package silAST.methods

import collection.Set
import silAST.types.{DataTypeFactory, DataType}
import silAST.domains.{DomainFunction, DomainPredicate, DomainTemplateFactory}
import silAST.expressions.ExpressionFactory
import silAST.programs.{ProgramFactory, NodeFactory}
import silAST.programs.symbols.{Field, ProgramVariable, Function, Predicate}

trait ScopeFactory
  extends NodeFactory
  with DataTypeFactory
  with ExpressionFactory {
  /////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////
  private[silAST] def programFactory: ProgramFactory

  protected[silAST] def parentFactory: Option[ScopeFactory]

  def programVariables: Set[ProgramVariable]

  def inputProgramVariables: Set[ProgramVariable]

  def outputProgramVariables: Set[ProgramVariable]

  def functions: Set[Function] = parentFactory.get.functions

  def predicates: Set[Predicate] = parentFactory.get.predicates

  def domainFunctions: Set[DomainFunction] = parentFactory.get.domainFunctions

  def domainPredicates: Set[DomainPredicate] = parentFactory.get.domainPredicates

  def fields: Set[Field] = parentFactory.get.fields

  override def dataTypes: Set[DataType] = parentFactory.get.dataTypes union pDataTypes

  protected[silAST] def methodFactories: Set[MethodFactory] = parentFactory.get.methodFactories

  protected[silAST] override def domainFactories: Set[DomainTemplateFactory] = parentFactory.get.domainFactories

  //  private[silAST] val pScope: Scope
}