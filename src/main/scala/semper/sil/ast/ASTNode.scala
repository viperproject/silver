package semper.sil.ast

import source.SourceLocation

abstract class ASTNode protected[sil] {
  def sourceLocation: SourceLocation
  def comment: scala.collection.immutable.List[String] //comments
}