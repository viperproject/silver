package silAST.types

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}
import silAST.domains.{DomainFactory, Domain}

abstract sealed class DataType(sl: SourceLocation) extends ASTNode(sl) {

}

final case class ReferenceDataType private[silAST]() extends DataType(noLocation) with AtomicNode {
  override val toString = "ref"
}

object ReferenceDataType {
  val referenceType: ReferenceDataType = new ReferenceDataType
}

case class NonReferenceDataType private[silAST](
    sl: SourceLocation,
    private[silAST] val domainFactory : DomainFactory)
  extends DataType(sl) with AtomicNode
{
  override val toString = domain.name

  def domain = if (domainFactory.compiled) domainFactory.domain else throw new Exception("domain \""+domainFactory.name+"\" not compiled")
}