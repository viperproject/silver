package silAST.types

import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.{noLocation, SourceLocation}

abstract sealed class DataType(sl: SourceLocation) extends ASTNode(sl) {

}

final case class ReferenceDataType private[silAST]() extends DataType(noLocation) with AtomicNode {
  override def toString = "ref"
}

object ReferenceDataType {
  val referenceType: ReferenceDataType = new ReferenceDataType
}


abstract case class NonReferenceDataType(sl: SourceLocation) extends DataType(sl) {
}