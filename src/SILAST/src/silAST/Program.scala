package silAST

import scala.collection.Seq

abstract class Program(
		val sl : SourceLocation
	) extends ASTNode(SourceLocation) {

  def toString(): String

  def subNodes(): Seq[ASTNode]

}