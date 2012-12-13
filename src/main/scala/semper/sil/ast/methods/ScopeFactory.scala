package semper.sil.ast.methods

import collection.Set
import semper.sil.ast.types.{DataTypeFactory, DataType}
import semper.sil.ast.domains.{DomainFunction, DomainPredicate, DomainTemplateFactory}
import semper.sil.ast.expressions.ExpressionFactory
import semper.sil.ast.programs.{ProgramFactory, NodeFactory}
import semper.sil.ast.programs.symbols.{Field, ProgramVariable, Function, Predicate}

trait ScopeFactory
  extends NodeFactory
  with DataTypeFactory
  with ExpressionFactory {
  /////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////
  private [sil] def programFactory: ProgramFactory

  protected[sil] def parentFactory: Option[ScopeFactory]

  def programVariables: Set[ProgramVariable]

  def inputProgramVariables: Set[ProgramVariable]

  def outputProgramVariables: Set[ProgramVariable]

  def functions: Set[Function] = parentFactory.get.functions

  def predicates: Set[Predicate] = parentFactory.get.predicates

  def domainFunctions: Set[DomainFunction] = parentFactory.get.domainFunctions

  def domainPredicates: Set[DomainPredicate] = parentFactory.get.domainPredicates

  def fields: Set[Field] = parentFactory.get.fields

  override def dataTypes: Set[DataType] = parentFactory.get.dataTypes union pDataTypes

  protected[sil] def methodFactories: Set[MethodFactory] = parentFactory.get.methodFactories

  protected[sil] override def domainFactories: Set[DomainTemplateFactory] = parentFactory.get.domainFactories

  //  private[semper.sil.ast] val pScope: Scope
}