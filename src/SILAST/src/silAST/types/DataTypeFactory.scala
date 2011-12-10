package silAST.types

import silAST.programs.NodeFactory
import collection.Set
import collection.mutable.HashSet
import silAST.source.SourceLocation
import silAST.domains.DomainFactory


trait DataTypeFactory extends NodeFactory {

  def makeNonReferenceDataType(sl: SourceLocation, df: DomainFactory,ta : DataTypeSequence): NonReferenceDataType = {
    require(domainFactories contains df)
    require(ta.forall(dataTypes contains _))
    require(df.domain.typeParameters.length == ta.length)
    val result = new NonReferenceDataType(sl, df.domain,ta)
    pDataTypes += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  def makeDataTypeSequence(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes contains _))

    val result = new DataTypeSequence(types)
    dataTypeSequences += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeVariableType(sl: SourceLocation, variable : TypeVariable): VariableType =
  {
    require(typeVariables contains  variable)

    val result = new VariableType(sl,variable)
    pDataTypes += result
    result
  }

  protected[silAST] val pDataTypes = new HashSet[DataType]
  pDataTypes += integerType
  pDataTypes += permissionType

  protected[silAST] def domainFactories: Set[DomainFactory] //= new HashSet[DomainFactory]
  protected[silAST] def dataTypes: Set[DataType] //= pDataTypes //new HashSet[DataType]
  protected[silAST] final val dataTypeSequences = new HashSet[DataTypeSequence]

  protected[silAST] def typeVariables : Set[TypeVariable]
}