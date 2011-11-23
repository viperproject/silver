package silAST.symbols.logical
import silAST.source.SourceLocation

class ImplicationOperatorNode(sl:SourceLocation) extends BinaryBooleanOperatorNode(sl) {

  def name : String = { return "==>" }

}