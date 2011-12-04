package silAST.types

import silAST.programs.NodeFactory
import collection.mutable.HashSet
import silAST.expressions.terms.Term
import silAST.expressions.util.TermSequence
import silAST.source.SourceLocation
import silAST.domains.{Domain, DomainFactory}


trait DataTypeFactory extends NodeFactory{
  dataTypes += ReferenceDataType.referenceType

  def makeNonReferenceDataType(sl : SourceLocation, df : DomainFactory) : NonReferenceDataType =
  {
    require (domainFactories contains df)
    val result = new NonReferenceDataType(sl,df)
    dataTypes += result
    result
  }

  def makeReferenceDataType() : ReferenceDataType = ReferenceDataType.referenceType

  protected[silAST] val domainFactories = new HashSet[DomainFactory]
  protected[silAST] val dataTypes = new HashSet[DataType]
  protected[silAST] val dataTypeSequences = new HashSet[DataTypeSequence]
}