package silAST.programs {

import silAST.methods.MethodFactory
import silAST.source.{noLocation, SourceLocation}
import silAST.domains._
import symbols._
import silAST.types._
import scala.collection.mutable.HashSet

final class ProgramFactory(
                            val sourceLocation : SourceLocation,
                            val name: String
                            ) extends NodeFactory with ScopeFactory //DataTypeFactory
{
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getProgram: Program = {
    for (df <- domainFactories) df.compile()
    for (pf <- predicateFactories) pf.compile()
    for (mf <- methodFactories) mf.compile()
    for (ff <- functionFactories) ff.compile()

    new Program(sourceLocation, name, domains, fields, functions, predicates, (for (mf <- methodFactories) yield mf.method).toSet, this)
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getDomainFactory(name: String,typeVariableNames :Seq[(SourceLocation,String)])(implicit sourceLocation : SourceLocation): DomainFactory = {
    require(domainFactories.forall(_.name != name))
    val result = new DomainFactory(this, sourceLocation, name,typeVariableNames)
    domainFactories += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def getMethodFactory(sourceLocation : SourceLocation, name: String): MethodFactory = {
    require(methodFactories.forall(_.name != name))
    val result = new MethodFactory(this, sourceLocation, name)
    methodFactories += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def getPredicateFactory(sourceLocation : SourceLocation, name: String): PredicateFactory = {
    require(predicateFactories.forall(_.name != name))
    val result = new PredicateFactory(this, sourceLocation, name)
    predicateFactories += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def getFunctionFactory(sourceLocation : SourceLocation, name: String, params: Seq[(SourceLocation, String, DataType)], resultType: DataType): FunctionFactory = {
    require(functionFactories.forall(_.name != name))
    require(params.forall(dataTypes contains _._3))
    require(params.forall((x) => params.forall((y) => x == y || x._2 != y._2)))
    val result = new FunctionFactory(this, sourceLocation, name, params, resultType)
    functionFactories += result
    result
  }

  def makeDomainInstance(factory: DomainFactory, ta: DataTypeSequence) : Domain = 
  {
    require(ta.forall(dataTypes contains _))
    var r = factory.getInstance(ta)
    pDomains += r
    r
  }


  //////////////////////////////////////////////////////////////////////////
  //@Symbol construction
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def defineField(sourceLocation : SourceLocation, name: String, dataType: DataType): Field = {
    require(fields.forall(_.name != name))
    require(dataTypes contains dataType)
    require(dataType.freeTypeVariables.isEmpty)
    defineField(
      dataType match{
        case d : NonReferenceDataType => new NonReferenceField(sourceLocation, name, d)
        case r : ReferenceDataType    => new ReferenceField(sourceLocation,name)
        case _ => throw new Exception("Tried to create field of non groud type")
      }
    )
  }

  //////////////////////////////////////////////////////////////////////////
  private def defineField(f: Field): Field = {
    fields += f
    f
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] override val domainFactories = new HashSet[DomainFactory]
  protected[silAST] override val methodFactories = new HashSet[MethodFactory]
  
  protected[silAST] val predicateFactories = new HashSet[PredicateFactory]
  protected[silAST] val functionFactories = new HashSet[FunctionFactory]

  protected[silAST] val fields: collection.mutable.Set[Field] = new HashSet[Field]

  protected[silAST] override def functions: Set[Function] = (for (ff <- functionFactories) yield ff.pFunction).toSet

  protected[silAST] override def predicates = (for (pf <- predicateFactories) yield pf.pPredicate).toSet

/*  pDataTypes += integerType
  pDataTypes += permissionType
  pDataTypes += referenceType
*/
  override def dataTypes : collection.Set[DataType]=
    pDataTypes ++ 
//    Set(integerType,permissionType,referenceType,booleanType) ++
    (for (d <- domains) yield d.getType).toSet

  def emptyDTSequence = new DataTypeSequence(List.empty[DataType])

  private[silAST] val pDomains : HashSet[Domain] = HashSet(integerDomain,permissionDomain,referenceDomain,booleanDomain)
  protected[silAST] def domains: collection.Set[Domain] =
    pDomains ++
      ( for (df <- domainFactories) yield df.domain).toSet ++
      ( for (df <- domainFactories) yield df.domain.pInstances.values).flatten


  protected[silAST] override def domainFunctions: collection.Set[DomainFunction] =
    (for (f <- (for (d <- domains) yield d.functions).flatten) yield f) +
      (nullFunction)

  //TODO:check duplicate names/prefix names

  protected[silAST] override def domainPredicates: collection.Set[DomainPredicate] =
    (for (p <- (for (d <- domains) yield d.predicates).flatten) yield p)

  override def parentFactory = None

  override val typeVariables = collection.Set[TypeVariable]()
  override val programVariables = collection.Set[ProgramVariable]()
}

}


