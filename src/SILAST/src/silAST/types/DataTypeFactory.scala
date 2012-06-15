package silAST.types

import silAST.programs.NodeFactory
import collection.{mutable, Set}
import collection.mutable.HashSet
import silAST.source.SourceLocation
import silAST.domains.DomainTemplateFactory


trait DataTypeFactory extends NodeFactory {

  //////////////////////////////////////////////////////////////////////////
  protected[silAST] def migrate(dts: DataTypeSequence) {
    dts.foreach(migrate(_))
  }

  protected[silAST] def migrate(dt: DataType) {
    if (dataTypes contains dt)
      return

    dt match {
      case nr: NonReferenceDataType => {
        require(domainFactories.exists(_.pDomainTemplate == nr.domain))
        pDataTypes += nr
        return
      }
      case r: ReferenceDataType => {
        pDataTypes += r
        return
      }
      case vt: VariableType => {
        require(typeVariables contains vt.variable)
        pDataTypes += vt
        return
      }
    }
  }

  def makeNonReferenceDataType(df: DomainTemplateFactory, ta: DataTypeSequence,sourceLocation: SourceLocation,comment:List[String] = Nil): NonReferenceDataType = {
    require(domainFactories contains df)
    migrate(ta)
    //    require(ta.forall(dataTypes contains _))
    require(df.pDomainTemplate.typeParameters.length == ta.length)
    val domain = df.pDomainTemplate.getInstance(ta)
    val result = new NonReferenceDataType(domain)(sourceLocation,comment)
    pDataTypes += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeVariableType(variable: TypeVariable,sourceLocation: SourceLocation,comment : List[String] = Nil): VariableType = {
    require(typeVariables contains variable)

    val result = new VariableType(variable)(sourceLocation,comment)
    pDataTypes += result
    result
  }

  protected[silAST] val pDataTypes = new mutable.HashSet[DataType] //(integerType,permissionType)
  //  pDataTypes += integerType
  //  pDataTypes += permissionType

  protected[silAST] def domainFactories: Set[DomainTemplateFactory] //= new HashSet[DomainTemplateFactory]
  protected[silAST] def dataTypes: Set[DataType] //= pDataTypes //new HashSet[DataType]
  protected[silAST] final val dataTypeSequences = new mutable.HashSet[DataTypeSequence]

  protected[silAST] def typeVariables: Set[TypeVariable]
}