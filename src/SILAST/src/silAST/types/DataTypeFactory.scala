package silAST.types

import silAST.programs.NodeFactory
import collection.Set
import collection.mutable.HashSet
import silAST.source.SourceLocation
import silAST.domains.DomainFactory


trait DataTypeFactory extends NodeFactory {

  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(dts : DataTypeSequence)
  {
    dts.foreach(migrate(_))
  }

  protected[silAST] def migrate(dt : DataType)
  {
    if (dataTypes contains dt)
      return

    dt match{
      case nr : NonReferenceDataType => {
        require(domainFactories.exists (_.domain == nr.domain))
        pDataTypes += nr;
        return;
      }
      case r : ReferenceDataType => {
        pDataTypes += r;
        return;
      }
      case vt : VariableType => {
        require(typeVariables contains  vt.variable)
        pDataTypes += vt;
        return;
      }
    }
  }

  def makeNonReferenceDataType(df: DomainFactory,ta : DataTypeSequence)(sourceLocation : SourceLocation): NonReferenceDataType = {
    require(domainFactories contains df)
    migrate(ta)
//    require(ta.forall(dataTypes contains _))
    require(df.domain.typeParameters.length == ta.length)
    val domain = df.domain.getInstance(ta)
    val result = new NonReferenceDataType(domain)(sourceLocation)
    pDataTypes += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeVariableType(variable : TypeVariable)(sourceLocation : SourceLocation): VariableType =
  {
    require(typeVariables contains  variable)

    val result = new VariableType(variable)(sourceLocation)
    pDataTypes += result
    result
  }

  protected[silAST] val pDataTypes = new HashSet[DataType] //(integerType,permissionType)
//  pDataTypes += integerType
//  pDataTypes += permissionType

  protected[silAST] def domainFactories: Set[DomainFactory] //= new HashSet[DomainFactory]
  protected[silAST] def dataTypes: Set[DataType] //= pDataTypes //new HashSet[DataType]
  protected[silAST] final val dataTypeSequences = new HashSet[DataTypeSequence]

  protected[silAST] def typeVariables : Set[TypeVariable]
}