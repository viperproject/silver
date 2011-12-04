package silAST.programs {

import silAST.source.SourceLocation
import silAST.domains.DomainFactory
import silAST.expressions.ExpressionFactory
import silAST.types.{DataTypeSequence, NonReferenceDataType, DataType}
import silAST.methods.MethodFactory
import collection.mutable.{HashSet, HashMap,Set}
import symbols._

final class ProgramFactory(
                            val name: String
                            ) extends NodeFactory with ExpressionFactory
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
  def makeMethod(sl : SourceLocation, name: String): MethodFactory = {
    require (!methodFactories.contains(name))
    val result = new MethodFactory(this,sl,name)
    methodFactories += name -> result
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

  private def defineField(f : Field) : Field = {
    fields += f
    f
  }

  //////////////////////////////////////////////////////////////////////////
  def defineDataTypeSequence(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes.contains(_)))

    val result =new DataTypeSequence(types)
    dataTypeSequences += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  protected[silAST] val domainFactoryMap = new HashMap[String, DomainFactory]
  protected[silAST] val methodFactories = new HashMap[String, MethodFactory]

  protected[silAST] override val programVariables = Set.empty[ProgramVariable]
  protected[silAST] override val fields : Set[Field] = new HashSet[Field]
  protected[silAST] override val functions : Set[Function] = new HashSet[Function]
}

}


