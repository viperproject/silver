package silAST.expressions.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.AtomicNode
import silAST.expressions.ProgramTermNode
import silAST.source.SourceLocation

abstract class LiteralNode(sl:SourceLocation) extends ProgramTermNode(sl) with AtomicNode[LiteralNode]{
}