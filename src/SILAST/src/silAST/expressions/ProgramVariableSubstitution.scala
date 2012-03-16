package silAST.expressions

import silAST.symbols.logical.quantification.LogicalVariable
import silAST.programs.symbols.ProgramVariable
import silAST.source.{PVSubstitutedSourceLocation, SourceLocation}
import terms.{PTermFactory, PTerm, Term}


sealed abstract class ProgramVariableSubstitution
{
  type T <: Term

  val targetFactory: PTermFactory

  def mapVariable(v : ProgramVariable) : Option[T]
  protected[silAST] val varMap : Map[ProgramVariable,T]
  protected[silAST] val logicalVarMap : Map[LogicalVariable,LogicalVariable]
  def sourceLocation(sl : SourceLocation) : PVSubstitutedSourceLocation =
    new PVSubstitutedSourceLocation(sl,this)
}

private[silAST] sealed class ProgramVariableSubstitutionC[TT<:Term](
    override val targetFactory: PTermFactory,
    variables : Set[(ProgramVariable,TT)],
    logicalVariables : Set[(LogicalVariable,LogicalVariable)]
  )
  extends ProgramVariableSubstitution
{
  override type T = TT

  protected[silAST] override val varMap : Map[ProgramVariable,T] = variables.toMap

  override def toString = super.toString + varMap.mkString("(",",",")")

  def +(other : ProgramVariableSubstitution)  : ProgramVariableSubstitution =
  {
    require (other.targetFactory == targetFactory)
    new ProgramVariableSubstitutionC[Term](
      targetFactory,
      (varMap.++[Term](other.varMap)).toSet,
      (logicalVarMap.++(other.logicalVarMap)).toSet
    )
  }
  def mapVariable(v : ProgramVariable) : Option[T] = varMap.get(v)

  def mapLogicalVariable(v : LogicalVariable) : Option[LogicalVariable] = logicalVarMap.get(v)
  protected[silAST] override val logicalVarMap : Map[LogicalVariable,LogicalVariable] = logicalVariables.toMap
}


sealed trait PProgramVariableSubstitution extends ProgramVariableSubstitution
{
  override type T <: PTerm
}

private[silAST] sealed class PProgramVariableSubstitutionC(
    override val targetFactory: PTermFactory,
    variables : Set[(ProgramVariable,PTerm)],
    logicalVariables : Set[(LogicalVariable,LogicalVariable)]
  )
  extends ProgramVariableSubstitutionC[PTerm](targetFactory,variables,logicalVariables)
  with PProgramVariableSubstitution
{
}
