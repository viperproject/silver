package semper.sil.ast.domains

import collection.Set
import semper.sil.ast.symbols.logical.quantification.LogicalVariable
import semper.sil.ast.types.{DataType, TypeVariable}
import semper.sil.ast.expressions.terms._
import semper.sil.ast.source._


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class TypeVariableSubstitution {
//  def sourceLocation: SourceLocation

  def typeVariables: Set[TypeVariable]

//  def newDomain: Domain

  def mapType(v: TypeVariable, t: DataType): DataType

  def mapVariable(v: LogicalVariable): Option[LogicalVariable]

  private [sil] def types: Set[(TypeVariable, DataType)]

  protected[sil] val varMap: Map[LogicalVariable, LogicalVariable]

  def sourceLocation(sl: SourceLocation): TypeSubstitutedSourceLocation =
    new TypeSubstitutedSourceLocation(sl, this)

  def +(other: TypeVariableSubstitution): TypeVariableSubstitution
}

private [sil] class TypeSubstitutionC[Term](
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
trait LogicalVariableSubstitution {//extends TypeVariableSubstitution {
  type T <: Term

  def types: Set[(TypeVariable, DataType)]

  def +(other: LogicalVariableSubstitution): LogicalVariableSubstitution

  //   private[semper.sil.ast] def variables : Set[(LogicalVariable,T)]

  def mapVariable(v: LogicalVariable): Option[T] //= varMap.get(v)
  protected[sil] def varMap: Map[LogicalVariable, T]
  protected[sil] def variables : Set[(LogicalVariable,T)]

  def sourceLocation(sl: SourceLocation): LogicalSubstitutedSourceLocation = new LogicalSubstitutedSourceLocation(sl, this)
}

private [sil] class LogicalVariableSubstitutionC[TT <: Term](
                                                                override val types: Set[(TypeVariable, DataType)],
                                                                override val variables: Set[(LogicalVariable, TT)]
                                                                ) extends LogicalVariableSubstitution {
  override def toString = super.toString + varMap.mkString("(", ",", ")")

  override type T = TT
  require(variables.forall((x) => variables.count((y) => y._1 == x._1) == 1))

  override def +(other: LogicalVariableSubstitution): LogicalVariableSubstitution =
    new LogicalVariableSubstitutionC[Term](types ++ other.types, (varMap ++ other.varMap).toSet /*,newDomain*/)

  protected[sil] override val varMap: Map[LogicalVariable, TT] = variables.toMap

  def mapVariable(v: LogicalVariable): Option[TT] = varMap.get(v)
}

trait PLogicalVariableSubstitution extends LogicalVariableSubstitution {
  override type T <: PTerm

  def mapVariable(v: LogicalVariable): Option[T]

  def +(other: PLogicalVariableSubstitution): PLogicalVariableSubstitution =
    new PLogicalVariableSubstitutionC(types ++ other.types, varMap.toSet ++ other.varMap.toSet /*,newDomain*/)
}

private [sil] class PLogicalVariableSubstitutionC(
                                                     override val types: Set[(TypeVariable, DataType)],
                                                     variables: Set[(LogicalVariable, PTerm)]
                                                     ) extends LogicalVariableSubstitutionC(types, variables /*,newDomain*/) with PLogicalVariableSubstitution {

}

trait DLogicalVariableSubstitution extends LogicalVariableSubstitution {
  override type T <: DTerm

  def mapVariable(v: LogicalVariable): Option[T]

  def +(other: DLogicalVariableSubstitution): DLogicalVariableSubstitution =
    new DLogicalVariableSubstitutionC(types ++ other.types, varMap.toSet ++ other.varMap.toSet /*,newDomain*/)
}

private [sil] class DLogicalVariableSubstitutionC(
                                                     types: Set[(TypeVariable, DataType)],
                                                     variables: Set[(LogicalVariable, DTerm)] //,
                                                     //                                      newDomain : Domain
                                                     ) extends LogicalVariableSubstitutionC(types, variables /*, newDomain*/) with DLogicalVariableSubstitution {
}

class GLogicalVariableSubstitution private [sil](
                                                    types: Set[(TypeVariable, DataType)],
                                                    variables: Set[(LogicalVariable, GTerm)] //,
                                                    //                                           newDomain : Domain
                                                    ) extends LogicalVariableSubstitutionC[GTerm](types, variables /*,newDomain*/)
with PLogicalVariableSubstitution with DLogicalVariableSubstitution {
  override type T = GTerm

  def +(other: GLogicalVariableSubstitution): GLogicalVariableSubstitution =
    new GLogicalVariableSubstitution(types ++ other.types, variables ++ other.varMap.toSet /*,newDomain*/)
}
