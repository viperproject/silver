package silAST

import scala.collection.Seq

abstract class Literal(sl:SourceLocation) extends ASTNode(sl) with AtomicNode{
}