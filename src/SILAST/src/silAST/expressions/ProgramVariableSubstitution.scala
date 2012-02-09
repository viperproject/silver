package silAST.expressions

import silAST.types.{DataType, TypeVariable}
import silAST.symbols.logical.quantification.BoundVariable
import silAST.programs.symbols.ProgramVariable
import terms.{PTerm, Term}


sealed abstract class ProgramVariableSubstitution
{
  type T <: Term
  def +(other : ProgramVariableSubstitution)  : ProgramVariableSubstitution

  def mapVariable(v : ProgramVariable) : Option[T]
  protected[silAST] val varMap : Map[ProgramVariable,T]
}

private[silAST] sealed class ProgramVariableSubstitutionC[TT<:Term](variables : Set[(ProgramVariable,TT)])
  extends ProgramVariableSubstitution
{
  override type T = TT

  protected[silAST] override val varMap : Map[ProgramVariable,T] = variables.toMap

  override def toString = super.toString + varMap.mkString("(",",",")")

  def +(other : ProgramVariableSubstitution)  : ProgramVariableSubstitution =
    new ProgramVariableSubstitutionC[Term]((varMap.++[Term](other.varMap)).toSet)

  def mapVariable(v : ProgramVariable) : Option[T] = varMap.get(v)
}


sealed trait PProgramVariableSubstitution extends ProgramVariableSubstitution
{
  override type T <: PTerm
  def +(other : PProgramVariableSubstitution)  : PProgramVariableSubstitution
}

private[silAST] sealed class PProgramVariableSubstitutionC(variables : Set[(ProgramVariable,PTerm)])
  extends ProgramVariableSubstitutionC[PTerm](variables) with PProgramVariableSubstitution
{
  def +(other : PProgramVariableSubstitution)  : PProgramVariableSubstitution =
    new PProgramVariableSubstitutionC((varMap.++[PTerm](other.varMap)).toSet)
}
