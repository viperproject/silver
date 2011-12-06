package silAST.programs.symbols

import silAST.ASTNode
import scala.collection.Seq
import silAST.source.SourceLocation

final class ProgramVariableSequence private[silAST](
                                                     sl: SourceLocation,
                                                     val variables: Seq[ProgramVariable]
                                                     ) extends ASTNode(sl) with Seq[ProgramVariable]
{
  override def toString() = "(" + variables.mkString(",") + ")"
  def toStringWithTypes() = "(" + (for (v <- variables) yield (v.name + " : " + v.dataType.toString)).mkString(",") + ")"

  def subNodes: Seq[ASTNode] = variables

  override def length: Int = variables.length
  override def apply(idx: Int): ProgramVariable = variables(idx)
  override def iterator = variables.iterator
}