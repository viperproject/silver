package silAST.symbols.logical
import silAST.source.SourceLocation

class AndOperatorNode(sl:SourceLocation) extends BinaryBooleanOperatorNode(sl) {

  def name : String = { return "&&" }

}