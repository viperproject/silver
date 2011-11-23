package silAST.symbols.logical
import silAST.source.SourceLocation

class NotOperatorNode(sl:SourceLocation) extends UnaryBooleanOperatorNode(sl) {

  def name : String = { return "!" }

}