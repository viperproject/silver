package silAST.programs {

import silAST.source.SourceLocation
import silAST.domains.DomainFactory
import silAST.methods.MethodFactory
import collection.mutable.{HashSet, HashMap,Set}
import symbols._
import silAST.types.{ReferenceDataType, DataType, DataTypeFactory, NonReferenceDataType}

final class ProgramFactory(
                            val name: String
                            ) extends NodeFactory with DataTypeFactory//with ExpressionFactory
{
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getDomainFactory(name: String): DomainFactory = {
    require (!domainFactoryMap.contains(name))
    val result = new DomainFactory(this,name)
    domainFactoryMap += name -> result
    domainFactories += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def getMethodFactory(sl : SourceLocation, name: String): MethodFactory = {
    require (!methodFactories.contains(name))
    val result = new MethodFactory(this,sl,name)
    methodFactories += name -> result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def getPredicateFactory(sl : SourceLocation, name: String): PredicateFactory = {
    require (!predicateFactories.contains(name))
    val result = new PredicateFactory(this,sl,name)
    predicateFactories += name -> result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  //@Symbol construction
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def defineDomainField(sl: SourceLocation, name: String, dataType: NonReferenceDataType): Field = {
    require(fields.forall(_.name!=name))
    require(dataTypes.contains(dataType))
    defineField(new NonReferenceField(sl, name, dataType))
  }

  //////////////////////////////////////////////////////////////////////////
  def defineReferenceField(sl: SourceLocation, name: String): Field = {
    require(fields.forall(_.name!=name))
    defineField(new ReferenceField(sl, name))
  }

  //////////////////////////////////////////////////////////////////////////
  private def defineField(f : Field) : Field = {
    fields += f
    f
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] val domainFactoryMap = new HashMap[String, DomainFactory]
  protected[silAST] val methodFactories = new HashMap[String, MethodFactory]
  protected[silAST] val predicateFactories = new HashMap[String, PredicateFactory]

  protected[silAST] val fields : Set[Field] = new HashSet[Field]
  protected[silAST] val functions : Set[Function] = new HashSet[Function]
  protected[silAST] val predicates : Set[Predicate] = new HashSet[Predicate]

  protected[silAST] override val dataTypes = new HashSet[DataType]
  dataTypes += ReferenceDataType.referenceType
}

}


