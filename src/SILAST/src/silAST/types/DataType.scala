package silAST.types

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}
import silAST.domains.{Domain, DomainFactory}

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
    domain : Domain)
  extends DataType(sl) with AtomicNode
{
  override val toString = domain.name
}