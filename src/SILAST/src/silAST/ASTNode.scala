package silAST

import source.SourceLocation

//TODO: check equality/hashCode
abstract class ASTNode protected[silAST] {
  def sourceLocation: SourceLocation

  override def toString: String //String representation

  override def equals(other: Any): Boolean

  override def hashCode(): Int
}