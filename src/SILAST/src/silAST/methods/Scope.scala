package silAST.methods

import silAST.ASTNode
import collection.mutable.ListBuffer
import silAST.programs.symbols.ProgramVariable

trait Scope
  extends ASTNode
{
  def parentScope: Option[Scope]

  def locals : Set[ProgramVariable] = pLocals.toSet
  def inheritedVariables : collection.Set[ProgramVariable] =
    (parentScope match {
      case Some(s) => s.programVariables
      case _ => Set[ProgramVariable]()
    })

  def programVariables: collection.Set[ProgramVariable] =
    locals union inheritedVariables

  def factory: ScopeFactory

  private[silAST] val pLocals = new ListBuffer[ProgramVariable]


}
