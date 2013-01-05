package semper.sil.ast.programs

import semper.sil.ast.source.SourceLocation
import semper.sil.ast.ASTNode
import collection.mutable


private[sil] trait NodeFactory {
  protected val nodeMap = new mutable.HashMap[SourceLocation, ASTNode]
}