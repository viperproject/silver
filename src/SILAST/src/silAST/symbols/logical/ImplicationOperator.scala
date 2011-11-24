package silAST.symbols.logical
import silAST.source.SourceLocation

class ImplicationOperator(sl:SourceLocation) extends BinaryBooleanOperator(sl) {

  def name : String = { return "==>" }

}