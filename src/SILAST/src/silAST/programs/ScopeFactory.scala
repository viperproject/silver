package silAST.programs
import collection.Set
import silAST.types.{DataTypeFactory,DataType}
import silAST.methods.MethodFactory
import silAST.domains.{DomainFunction,DomainPredicate,DomainFactory}
import silAST.programs.symbols.{ProgramVariable,Function,Predicate}
import silAST.expressions.terms.PTerm
import silAST.expressions.ProgramVariableSubstitution

trait ScopeFactory
  extends NodeFactory
  with DataTypeFactory
{
  protected[silAST] def parentFactory : Option[ScopeFactory]

  protected[silAST]          def methodFactories  : Set[MethodFactory]   = parentFactory.get.methodFactories
  protected[silAST]          def programVariables : Set[ProgramVariable] = parentFactory.get.programVariables
  protected[silAST] override def domainFactories  : Set[DomainFactory]   = parentFactory.get.domainFactories

  protected[silAST]          def functions  : Set[Function]  = parentFactory.get.functions
  protected[silAST]          def predicates : Set[Predicate] = parentFactory.get.predicates
                    override def dataTypes  : Set[DataType]  = parentFactory.get.dataTypes union pDataTypes

  protected[silAST] def domainFunctions  : Set[DomainFunction]  = parentFactory.get.domainFunctions
  protected[silAST] def domainPredicates : Set[DomainPredicate] = parentFactory.get.domainPredicates
  
}