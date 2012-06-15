package silAST.programs

import collection.mutable.HashMap
import silAST.source.SourceLocation
import silAST.ASTNode
import collection.mutable


private[silAST] trait NodeFactory {
  protected val nodeMap = new mutable.HashMap[SourceLocation, ASTNode]
}