package silAST.types

import silAST.programs.NodeFactory
import collection.Set
import collection.mutable.HashSet
import silAST.source.SourceLocation
import silAST.domains.DomainFactory
import silAST.expressions.terms.{integerType, permissionType}


trait DataTypeFactory extends NodeFactory {

  def makeNonReferenceDataType(sl: SourceLocation, df: DomainFactory): NonReferenceDataType = {
    require(domainFactories contains df)
    val result = new NonReferenceDataType(sl, df.domain)
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

  protected[silAST] val pDataTypes = new HashSet[DataType]
  pDataTypes += integerType
  pDataTypes += permissionType

  protected[silAST] def domainFactories: Set[DomainFactory] //= new HashSet[DomainFactory]
  protected[silAST] def dataTypes: Set[DataType] //= pDataTypes //new HashSet[DataType]
  protected[silAST] final val dataTypeSequences = new HashSet[DataTypeSequence]
}