package semper.sil.ast.methods

import semper.sil.ast.ASTNode
import collection.mutable.ListBuffer
import semper.sil.ast.programs.symbols.ProgramVariable

trait Scope
  extends ASTNode {
  def parentScope: Option[Scope]

  def locals: Set[ProgramVariable] = pLocals.toSet

  def inheritedVariables: collection.Set[ProgramVariable] =
    (parentScope match {
      case Some(s) => s.programVariables
      case _ => Set[ProgramVariable]()
    })

  def programVariables: collection.Set[ProgramVariable] =
    locals union inheritedVariables

  def factory: ScopeFactory

  private[sil] val pLocals = new ListBuffer[ProgramVariable]


}
