package semper.sil.ast.domains

import collection.Set
import semper.sil.ast.symbols.logical.quantification.LogicalVariable
import semper.sil.ast.types.{DataType, TypeVariable}
import semper.sil.ast.source._
import semper.sil.ast.expressions.Expression


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class TypeVariableSubstitution {
  //  def sourceLocation: SourceLocation

  def typeVariables: Set[TypeVariable]

  //  def newDomain: Domain

  def mapType(v: TypeVariable, t: DataType): DataType

  def mapVariable(v: LogicalVariable): Option[LogicalVariable]

  private[sil] def types: Set[(TypeVariable, DataType)]

  protected[sil] val varMap: Map[LogicalVariable, LogicalVariable]

  def sourceLocation(sl: SourceLocation): TypeSubstitutedSourceLocation =
    new TypeSubstitutedSourceLocation(sl, this)

  def +(other: TypeVariableSubstitution): TypeVariableSubstitution
}

private[sil] class TypeSubstitutionC[Expression](
                                                  val types: Set[(TypeVariable, DataType)],
                                                  val variables: Set[(LogicalVariable, LogicalVariable)]
                                                  ) extends TypeVariableSubstitution {
  override def toString = typeMap.mkString("[", ",", "]")

  val typeVariables: Set[TypeVariable] = for (t <- types) yield t._1

  protected val typeMap = types.toMap

  def mapType(v: TypeVariable, t: DataType): DataType = typeMap.getOrElse(v, t)

  def mapVariable(v: LogicalVariable): Option[LogicalVariable] = varMap.get(v)

  protected[sil] override val varMap: Map[LogicalVariable, LogicalVariable] = variables.toMap

  override def +(other: TypeVariableSubstitution): TypeVariableSubstitution =
    new TypeSubstitutionC(types ++ other.types, (varMap ++ other.varMap).toSet)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
trait LogicalVariableSubstitution {
  //extends TypeVariableSubstitution {
  type T <: Expression

  def types: Set[(TypeVariable, DataType)]

  def +(other: LogicalVariableSubstitution): LogicalVariableSubstitution

  //   private[semper.sil.ast] def variables : Set[(LogicalVariable,T)]

  def mapVariable(v: LogicalVariable): Option[T]

  //= varMap.get(v)
  protected[sil] def varMap: Map[LogicalVariable, T]

  protected[sil] def variables: Set[(LogicalVariable, T)]

  def sourceLocation(sl: SourceLocation): LogicalSubstitutedSourceLocation = new LogicalSubstitutedSourceLocation(sl, this)
}

private[sil] class LogicalVariableSubstitutionC[TT <: Expression](
                                                                   override val types: Set[(TypeVariable, DataType)],
                                                                   override val variables: Set[(LogicalVariable, TT)]
                                                                   ) extends LogicalVariableSubstitution {
  override def toString = super.toString + varMap.mkString("(", ",", ")")

  override type T = TT
  require(variables.forall((x) => variables.count((y) => y._1 == x._1) == 1))

  override def +(other: LogicalVariableSubstitution): LogicalVariableSubstitution =
    new LogicalVariableSubstitutionC[Expression](types ++ other.types, (varMap ++ other.varMap).toSet /*,newDomain*/)

  protected[sil] override val varMap: Map[LogicalVariable, TT] = variables.toMap

  def mapVariable(v: LogicalVariable): Option[TT] = varMap.get(v)
}
