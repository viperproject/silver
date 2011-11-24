package silAST.symbols.logical
import silAST.source.SourceLocation

class OrOperator(sl:SourceLocation) extends BinaryBooleanOperator(sl) {

  def name : String = { return "||" }

}