package silAST.symbols.logical
import silAST.source.SourceLocation

class OrOperatorNode(sl:SourceLocation) extends BinaryBooleanOperatorNode(sl) {

  def name : String = { return "||" }

}