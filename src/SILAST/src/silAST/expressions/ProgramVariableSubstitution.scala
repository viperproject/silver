package silAST.expressions

import silAST.symbols.logical.quantification.LogicalVariable
import silAST.programs.symbols.ProgramVariable
import silAST.source.{PVSubstitutedSourceLocation, SourceLocation}
import terms._


sealed trait ProgramVariableSubstitution {
  type T <: Term

  //  def targetFactory: PTermFactory

  def mapVariable(v: ProgramVariable): Option[T]

  protected[silAST] def varMap: Map[ProgramVariable, T]

  def sourceLocation(sl: SourceLocation): PVSubstitutedSourceLocation =
    new PVSubstitutedSourceLocation(sl, this)

  def logicalVariables: Set[(LogicalVariable, LogicalVariable)]
}

private[silAST] sealed class ProgramVariableSubstitutionC[TT <: Term](
                                                                       //    override val targetFactory: TF,
                                                                       variables: Set[(ProgramVariable, TT)],
                                                                       override val logicalVariables: Set[(LogicalVariable, LogicalVariable)]
                                                                       )
  extends ProgramVariableSubstitution {
  override type T = TT

  protected[silAST] override val varMap: Map[ProgramVariable, T] = variables.toMap

  override def toString = super.toString + varMap.mkString("(", ",", ")")

  def +(other: ProgramVariableSubstitution): ProgramVariableSubstitution = {
    //    require (other.targetFactory == targetFactory)
    new ProgramVariableSubstitutionC[Term](
      (varMap.++[Term](other.varMap)).toSet,
      logicalVariables union other.logicalVariables
    )
  }

  def mapVariable(v: ProgramVariable): Option[T] = varMap.get(v)

  def mapLogicalVariable(v: LogicalVariable): Option[LogicalVariable] = logicalVarMap.get(v)

  protected[silAST] val logicalVarMap: Map[LogicalVariable, LogicalVariable] = logicalVariables.toMap
}


sealed trait PProgramVariableSubstitution extends ProgramVariableSubstitution {
  override type T <: PTerm
}

private[silAST] sealed class PProgramVariableSubstitutionC(
                                                            variables: Set[(ProgramVariable, PTerm)],
                                                            override val logicalVariables: Set[(LogicalVariable, LogicalVariable)]
                                                            )
  extends ProgramVariableSubstitutionC[PTerm](variables, logicalVariables)
  with PProgramVariableSubstitution {
}

/////////////////////////////////////////////////////////////////////////////////
sealed trait DProgramVariableSubstitution extends ProgramVariableSubstitution {
  override type T <: DTerm
}

private[silAST] sealed class DProgramVariableSubstitutionC(
                                                            variables: Set[(ProgramVariable, DTerm)],
                                                            override val logicalVariables: Set[(LogicalVariable, LogicalVariable)]
                                                            )
  extends ProgramVariableSubstitutionC[DTerm](variables, logicalVariables)
  with DProgramVariableSubstitution {
}
