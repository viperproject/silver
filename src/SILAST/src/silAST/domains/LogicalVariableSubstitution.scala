package silAST.domains

import collection.Set
import silAST.symbols.logical.quantification.BoundVariable
import silAST.source.{noLocation, SourceLocation}
import silAST.types.{DataType, TypeVariable}
import silAST.expressions.terms._


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
abstract class TypeSubstitution()
{
  def sourceLocation : SourceLocation
  def typeVariables : Set[TypeVariable]

  def newDomain : Domain

  def mapType(v : TypeVariable, t : DataType) : DataType
  private[silAST] def types : Set[(TypeVariable,DataType)]

}

private [silAST] class TypeSubstitutionC (
    val types : Set[(TypeVariable,DataType)],
    val sourceLocation : SourceLocation,
    val newDomain : Domain
  ) extends TypeSubstitution
{
  override def toString = typeMap.mkString("[",",","]")
  val typeVariables : Set[TypeVariable] = for (t <- types) yield t._1

  protected val typeMap = types.toMap
  def mapType    (v : TypeVariable, t : DataType) : DataType = typeMap.getOrElse(v,t)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
trait LogicalVariableSubstitution extends TypeSubstitution
{
   type T <: Term
   def types : Set[(TypeVariable,DataType)]
   def +(other : LogicalVariableSubstitution)  : LogicalVariableSubstitution

//   private[silAST] def variables : Set[(BoundVariable,T)]

   def mapVariable(v : BoundVariable) : Option[T] //= varMap.get(v)
   protected[silAST] def varMap : Map[BoundVariable,T]
}

private[silAST] class LogicalVariableSubstitutionC[TT<:Term](
                    types : Set[(TypeVariable,DataType)],
                    variables : Set[(BoundVariable,TT)],
                    newDomain : Domain
                    ) extends TypeSubstitutionC(types,noLocation,newDomain) with LogicalVariableSubstitution
{
  override def toString = super.toString + varMap.mkString("(",",",")")

  override type T = TT
  require (variables.forall((x)=>variables.count((y)=>y._1==x._1)==1))

  override def +(other : LogicalVariableSubstitution)  : LogicalVariableSubstitution =
    new LogicalVariableSubstitutionC[Term](types ++ other.types,(varMap ++ other.varMap).toSet,newDomain)

  protected[silAST] override val varMap : Map[BoundVariable,TT] = variables.toMap
  def mapVariable(v : BoundVariable) : Option[TT] = varMap.get(v)
}

trait PLogicalVariableSubstitution extends LogicalVariableSubstitution
{
  override type T <: PTerm
  def mapVariable(v : BoundVariable) : Option[T]
  def +(other : PLogicalVariableSubstitution)  : PLogicalVariableSubstitution =
    new PLogicalVariableSubstitutionC(types ++ other.types,varMap.toSet ++ other.varMap.toSet,newDomain)
}

private[silAST] class PLogicalVariableSubstitutionC(
    types : Set[(TypeVariable,DataType)],
    variables : Set[(BoundVariable,PTerm)],
    newDomain : Domain
  ) extends LogicalVariableSubstitutionC(types,variables,newDomain) with PLogicalVariableSubstitution
{

}

trait DLogicalVariableSubstitution extends LogicalVariableSubstitution
{
  override type T <: DTerm
  def mapVariable(v : BoundVariable) : Option[T]
  def +(other : DLogicalVariableSubstitution)  : DLogicalVariableSubstitution =
    new DLogicalVariableSubstitutionC(types ++ other.types,varMap.toSet ++ other.varMap.toSet,newDomain)
}

private[silAST] class DLogicalVariableSubstitutionC(
                                      types : Set[(TypeVariable,DataType)],
                                      variables : Set[(BoundVariable,DTerm)],
                                      newDomain : Domain
                                      ) extends LogicalVariableSubstitutionC(types,variables, newDomain) with DLogicalVariableSubstitution
{
}

class GLogicalVariableSubstitution private[silAST](
                                           types : Set[(TypeVariable,DataType)],
                                           variables : Set[(BoundVariable,GTerm)],
                                           newDomain : Domain
                                           ) extends LogicalVariableSubstitutionC[GTerm](types,variables,newDomain)
                                              with PLogicalVariableSubstitution with DLogicalVariableSubstitution
{
  override type T = GTerm
  def +(other : GLogicalVariableSubstitution)  : GLogicalVariableSubstitution =
    new GLogicalVariableSubstitution(types ++ other.types,variables ++ other.varMap.toSet,newDomain)
}
