package silAST.programs {

import silAST.methods.MethodFactory
import collection.{Set}
import collection.mutable.{HashSet, HashMap}
import symbols._
import silAST.source.{noLocation, SourceLocation}
import silAST.types._
import silAST.domains.{Domain, DomainFunctionSignature, DomainFunction, DomainFactory}
import silAST.expressions.{FalseExpression, TrueExpression}

final class ProgramFactory(
                            val sl : SourceLocation,
                            val name: String
                            ) extends NodeFactory with DataTypeFactory//with ExpressionFactory
{
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getDomainFactory(name: String)(implicit sl : SourceLocation) : DomainFactory = {
    require (!domainFactoryMap.contains(name))
    val result = new DomainFactory(this,sl,name)
    domainFactoryMap += name -> result
//    domainFactories += result
//    dataTypes += result.domain
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

  protected[silAST] val fields : collection.mutable.Set[Field] = new HashSet[Field]
  protected[silAST] val functions : Set[Function] = new HashSet[Function]
  protected[silAST] def predicates : Set[Predicate] = (for (pf <- predicateFactories.values) yield pf.pPredicate).toSet[Predicate]

  protected[silAST] override def dataTypes = pDataTypes

  val referenceType = ReferenceDataType.referenceType
  val emptyDTSequence = new DataTypeSequence(List.empty[DataType])
  private val nullSig = new DomainFunctionSignature(noLocation,emptyDTSequence,referenceType)

  val nullFunction = new DomainFunction(noLocation,"null",nullSig)

  def domains : Set[Domain] = for (df <- domainFactories) yield df.domain
  def domainFunctions : Map[String, DomainFunction] =
    (for (f <- (for (d <- domains) yield d.functions).flatten) yield (f.name,f)).toMap +
    (nullFunction.name -> nullFunction)
    //TODO:check duplicate names/prefix names

  dataTypes += referenceType

  val trueExpression = new TrueExpression
  val falseExpression = new FalseExpression

  override def domainFactories = domainFactoryMap.values.toSet

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getProgram : Program = {
    for (df <- domainFactories) df.compile()
    for (pf<-predicateFactories.values) pf.compile()
    for (mf<-methodFactories.values) mf.compile()

    new Program(sl, name,domains,fields,functions,predicates,(for (mf <- methodFactories.values) yield mf.method).toSet)
  }
}

}


