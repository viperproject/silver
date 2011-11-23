package silAST.symbols.logical
import silAST.source.SourceLocation

class Exists(
    sl : SourceLocation
   ) extends Quantifier(sl) {
	override def toString() : String = { return "exists"}
}