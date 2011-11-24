package silAST.symbols.logical.quantification
import silAST.source.SourceLocation

class Forall( sl : SourceLocation ) extends Quantifier(sl) {
	override def toString() : String = { return "forall"}
}