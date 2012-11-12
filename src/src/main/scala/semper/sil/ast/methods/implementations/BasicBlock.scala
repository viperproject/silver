package semper.sil.ast.methods.implementations

import scala.collection.Seq
import collection.mutable.ListBuffer
import semper.sil.ast.source.SourceLocation
import semper.sil.ast.methods.Scope
import semper.sil.ast.programs.symbols.ProgramVariable

final class BasicBlock private [sil]
(
  val cfg: ControlFlowGraph,
  val scope: Scope,
  val label: String,
  val factory: BasicBlockFactory
  )
(val sourceLocation: SourceLocation,override val comment : List[String])
  extends Block {

  def statements: Seq[Statement] = pStatements.result()

  override val implementation = cfg.implementation

  private val pStatements = new ListBuffer[Statement]

  private [sil] def appendStatement(s: Statement) = {
    require((pStatements.forall(_ ne s))  )
    pStatements += s
  }

  override def readVariables: Set[ProgramVariable] =
    (for (s <- statements) yield s.readVariables).flatten.toSet[ProgramVariable] union
      (for (s <- successors) yield s.condition.programVariables).flatten.toSet

  override def writtenVariables: Set[ProgramVariable] = (for (s <- statements) yield s.writtenVariables).flatten.toSet

  /////////////////////////////////////////////////////////////////////////////////////////
  override def equals(other: Any): Boolean = {
    other match {
      case b: BasicBlock => b eq this
      case _ => false
    }
  }

  override def hashCode(): Int = statements.hashCode()


  override def toString = {
      def withComments(stmt : Statement) : List[String] = stmt.comment.map("// " + _) ++ List(stmt.toString)
      "\t" + label + ":{\n" +
        (if (!statements.isEmpty) statements.map(withComments).flatten.mkString("\t\t", "\n\t\t", "\n") else "") +
        controlFlowToString +
        "\t}\n"
    }

}
