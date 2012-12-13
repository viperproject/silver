package semper.sil.ast.programs.symbols

import semper.sil.ast.ASTNode
import scala.collection.Seq
import semper.sil.ast.source.SourceLocation

final class ProgramVariableSequence private [sil](
         val variables: Seq[ProgramVariable]
         )(val sourceLocation: SourceLocation,val comment:List[String])
  extends ASTNode
  with Seq[ProgramVariable]
{
  override def toString() = "(" + variables.mkString(",") + ")"

  def toStringWithTypes = "(" + (for (v <- variables) yield (v.name + " : " + v.dataType.toString)).mkString(",") + ")"

  def subNodes: Seq[ASTNode] = variables

  override def length: Int = variables.length

  override def apply(idx: Int): ProgramVariable = variables(idx)

  override def iterator = variables.iterator
}