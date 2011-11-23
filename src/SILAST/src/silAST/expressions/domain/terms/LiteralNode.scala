package silAST.expressions.domain.terms

import scala.collection.Seq
import silAST.ASTNode
import silAST.AtomicNode
import silAST.source.SourceLocation
import silAST.expressions.program.terms.GProgramTermNode
import silAST.expressions.program.terms.ProgramTermNode
import silAST.expressions.terms.AtomicTermNode

abstract class LiteralNode(sl:SourceLocation) extends GDomainTermNode[LiteralNode](sl) with AtomicNode[LiteralNode] with AtomicTermNode[LiteralNode]{
}