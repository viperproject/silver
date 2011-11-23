package silAST.symbols.logical
import silAST.source.SourceLocation

class Forall( sl : SourceLocation ) extends Quantifier(sl) {
	override def toString() : String = { return "forall"}
}