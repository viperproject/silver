package silAST.types

import silAST.programs.NodeFactory
import collection.mutable.HashSet
import silAST.source.SourceLocation
import silAST.domains.DomainFactory


trait DataTypeFactory extends NodeFactory{

  def makeNonReferenceDataType(sl : SourceLocation, df : DomainFactory) : NonReferenceDataType =
  {
    require (domainFactories contains df)
    val result = new NonReferenceDataType(sl,df.domain)
    dataTypes += result
    result
  }

  def makeReferenceDataType() : ReferenceDataType = ReferenceDataType.referenceType

  //////////////////////////////////////////////////////////////////////////
  def makeDataTypeSequence(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes.contains(_)))

    val result =new DataTypeSequence(types)
    dataTypeSequences += result
    result
  }

  protected[silAST] val domainFactories = new HashSet[DomainFactory]
  protected[silAST] val dataTypes = new HashSet[DataType]
  protected[silAST] val dataTypeSequences = new HashSet[DataTypeSequence]
}