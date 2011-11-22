package silAST.expressions.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.SourceLocation
import silAST.expressions.program.ProgramTermNode

abstract class LiteralNode(sl:SourceLocation) extends ProgramTermNode(sl) with AtomicNode[LiteralNode]{
}