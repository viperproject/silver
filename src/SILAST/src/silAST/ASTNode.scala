package silAST

import source.SourceLocation

abstract class ASTNode protected[silAST](
                                          val sourceLocation: SourceLocation
                                          ) {
  override def toString: String //String representation

  def subNodes: Seq[ASTNode] //Ordered subnodes
}