package silAST.symbols.logical.quantification
import silAST.source.SourceLocation
import silAST.ASTNode

sealed abstract class Quantifier( sl : SourceLocation) extends ASTNode(sl) {
	override def subNodes : Seq[ASTNode] = { return Nil }
}

case class Forall( sl : SourceLocation ) extends Quantifier(sl) {
	override def toString() : String = { return "forall"}
}

case class Exists(
    sl : SourceLocation
   ) extends Quantifier(sl) {
	override def toString() : String = { return "exists"}
}