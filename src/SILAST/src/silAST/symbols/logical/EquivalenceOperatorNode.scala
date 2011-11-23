package silAST.symbols.logical
import silAST.source.SourceLocation

class EquivalenceOperatorNode(sl:SourceLocation) extends BinaryBooleanOperatorNode(sl) {

  def name : String = { return "<==>" }

}