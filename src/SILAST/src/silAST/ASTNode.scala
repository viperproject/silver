package silAST

import source.SourceLocation

//TODO: check equality/hashCode
abstract class ASTNode protected[silAST](
                                          val sourceLocation: SourceLocation
                                          ) {
  override def toString: String //String representation
}