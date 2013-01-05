package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.types.{referenceType, DataType, NonReferenceDataType}

sealed abstract class Field private[sil] extends ASTNode {
  def name: String

  def dataType: DataType

  override def toString: String = "field " + name + " : " + dataType.toString
}

final case class ReferenceField private[sil](
                                              name: String
                                              )(override val sourceLocation: SourceLocation, val comment: List[String]) extends Field {
  override val dataType = referenceType
}

final case class NonReferenceField private[sil](
                                                 name: String,
                                                 dataType: NonReferenceDataType
                                                 )(override val sourceLocation: SourceLocation, val comment: List[String]) extends Field {
}