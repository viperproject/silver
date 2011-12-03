package silAST.types

import silAST.programs.NodeFactory
import collection.mutable.HashSet
import silAST.expressions.terms.Term
import silAST.expressions.util.TermSequence


trait DataTypeFactory extends NodeFactory{
  protected[silAST] val dataTypes = new HashSet[DataType]
  protected[silAST] val dataTypeSequences = new HashSet[DataTypeSequence]
}