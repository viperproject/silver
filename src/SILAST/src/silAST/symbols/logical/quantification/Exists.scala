package silAST.symbols.logical.quantification
import silAST.source.SourceLocation

class Exists(
    sl : SourceLocation
   ) extends Quantifier(sl) {
	override def toString() : String = { return "exists"}
}