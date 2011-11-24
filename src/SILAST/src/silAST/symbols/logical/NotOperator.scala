package silAST.symbols.logical
import silAST.source.SourceLocation

class NotOperator(sl:SourceLocation) extends UnaryBooleanOperator(sl) {

  def name : String = { return "!" }

}