package semper.sil.ast.types

import semper.sil.ast.programs.NodeFactory
import collection.{mutable, Set}
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.domains.DomainTemplateFactory


trait DataTypeFactory extends NodeFactory {

  //////////////////////////////////////////////////////////////////////////
  protected[sil] def migrate(dts: DataTypeSequence) {
    dts.foreach(migrate(_))
  }

  protected[sil] def migrate(dt: DataType) {
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

  def makeNonReferenceDataType(df: DomainTemplateFactory, ta: DataTypeSequence, sourceLocation: SourceLocation, comment: List[String] = Nil): NonReferenceDataType = {
    require(domainFactories contains df)
    migrate(ta)
    //    require(ta.forall(dataTypes contains _))
    require(df.pDomainTemplate.typeParameters.length == ta.length)
    val domain = df.pDomainTemplate.getInstance(ta)
    val result = new NonReferenceDataType(domain)(sourceLocation, comment)
    pDataTypes += result
    result
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def makeVariableType(variable: TypeVariable, sourceLocation: SourceLocation, comment: List[String] = Nil): VariableType = {
    require(typeVariables contains variable)

    val result = new VariableType(variable)(sourceLocation, comment)
    pDataTypes += result
    result
  }

  protected[sil] val pDataTypes = new mutable.HashSet[DataType] //(integerType,permissionType)
  //  pDataTypes += integerType
  //  pDataTypes += permissionType

  protected[sil] def domainFactories: Set[DomainTemplateFactory]

  //= new HashSet[DomainTemplateFactory]
  protected[sil] def dataTypes: Set[DataType]

  //= pDataTypes //new HashSet[DataType]
  protected[sil] final val dataTypeSequences = new mutable.HashSet[DataTypeSequence]

  protected[sil] def typeVariables: Set[TypeVariable]
}