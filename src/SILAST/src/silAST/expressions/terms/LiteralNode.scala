package silAST.expressions.terms

import scala.collection.Seq
import source.SourceLocation
import silAST.ASTNode
import silAST.AtomicNode

abstract class Literal(sl:SourceLocation) extends ASTNode(sl) with AtomicNode{
}