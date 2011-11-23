package silAST.symbols.logical
import silAST.source.SourceLocation
import silAST.ASTNode

abstract class Quantifier( sl : SourceLocation) extends ASTNode(sl) {
	override def subNodes : Seq[ASTNode] = { return Nil }
}