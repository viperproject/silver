package silAST.symbols.logical
import silAST.source.SourceLocation

class AndOperator(sl:SourceLocation) extends BinaryBooleanOperator(sl) {

  def name : String = { return "&&" }

}