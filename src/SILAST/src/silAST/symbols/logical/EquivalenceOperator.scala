package silAST.symbols.logical
import silAST.source.SourceLocation

class EquivalenceOperatorNode(sl:SourceLocation) extends BinaryBooleanOperator(sl) {

  def name : String = { return "<==>" }

}