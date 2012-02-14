package silAST

import source.SourceLocation

//TODO: check equality/hashCode
abstract class ASTNode protected[silAST]
{
  override def toString: String //String representation
  def sourceLocation : SourceLocation
}