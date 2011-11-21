package silAST

import scala.collection.Seq

abstract class Program(
		val sl : SourceLocation
	) extends ASTNode(sl) {

  def toString(): String

  def subNodes(): Seq[ASTNode]

}