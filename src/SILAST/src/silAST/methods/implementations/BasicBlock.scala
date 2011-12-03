package silAST.methods.implementations

import scala.collection.Seq
import silAST.ASTNode
import silAST.source.SourceLocation

final class BasicBlock private[silAST](
                                        sl: SourceLocation,
                                        val label: String,
                                        val statements: Seq[Statement],
                                        val predecessors: Set[CFGEdge],
                                        val successors: Set[CFGEdge]
                                        ) extends ASTNode(sl) {
  override def toString =
    "label:{\n" +
      statements.mkString("\n") +
      "goto " + (for (s <- successors) yield s.target.label).mkString(",") +
      "\n}\n"

  override def subNodes = statements
}
