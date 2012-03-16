package silAST.methods

import collection.Set
import implementations.ImplementationFactory
import silAST.types.{DataTypeFactory, DataType}
import silAST.domains.{DomainFunction, DomainPredicate, DomainFactory}
import silAST.source.SourceLocation
import silAST.expressions.ExpressionFactory
import silAST.programs.{ProgramFactory, NodeFactory}
import silAST.programs.symbols.{Field, ProgramVariable, Function, Predicate}

trait ScopeFactory
  extends NodeFactory
  with DataTypeFactory
  with ExpressionFactory
{
  /////////////////////////////////////////////////////////////////////////////////////
//  def scope: Scope // = pScope
/*
  /////////////////////////////////////////////////////////////////////////////////////
  def addProgramVariable(sourceLocation: SourceLocation, name: String, dataType: DataType) = {
    require(programVariables.forall(_.name != name))
    require(dataTypes contains dataType)

    val result = new ProgramVariable(sourceLocation, name, dataType)
    scope.pLocals.append(result)
    result
  }
  */
  /////////////////////////////////////////////////////////////////////////////////////
  /////////////////////////////////////////////////////////////////////////////////////
  private[silAST] def programFactory : ProgramFactory

  protected[silAST] def parentFactory: Option[ScopeFactory] //= scope.parentScope match
/*  {
    case Some(s) => Some(s.factory)
    case _ => None
  }
  */
  def programVariables: Set[ProgramVariable] // = scope.get.programVariables
  def functions: Set[Function] = parentFactory.get.functions
  def predicates: Set[Predicate] = parentFactory.get.predicates
  def domainFunctions: Set[DomainFunction] = parentFactory.get.domainFunctions
  def domainPredicates: Set[DomainPredicate] = parentFactory.get.domainPredicates
  def fields : Set[Field] = parentFactory.get.fields
  override def dataTypes: Set[DataType] = parentFactory.get.dataTypes union pDataTypes

  protected[silAST] def methodFactories: Set[MethodFactory] = parentFactory.get.methodFactories
  protected[silAST] override def domainFactories: Set[DomainFactory] = parentFactory.get.domainFactories
//  private[silAST] val pScope: Scope
}