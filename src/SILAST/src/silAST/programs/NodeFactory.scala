package silAST.programs

import collection.mutable.HashMap
import silAST.source.SourceLocation
import silAST.ASTNode


private[silAST] trait NodeFactory {
  protected val nodeMap = new HashMap[SourceLocation, ASTNode]
}