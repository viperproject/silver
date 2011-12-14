package silAST.domains

import collection.Set
import silAST.symbols.logical.quantification.BoundVariable
import silAST.source.{noLocation, SourceLocation}
import silAST.types.{DataType, TypeVariable}
import silAST.expressions.terms._


///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
class TypeSubstitution private [silAST] (private[silAST] val types : Set[(TypeVariable,DataType)],val sourceLocation : SourceLocation = noLocation)
{
  val typeVariables : Set[TypeVariable] = for (t <- types) yield t._1

  protected val typeMap = types.toMap
  def mapType    (v : TypeVariable, t : DataType) : DataType = typeMap.getOrElse(v,t)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
 abstract class Substitution private [silAST](
                                    types : Set[(TypeVariable,DataType)]
                                    ) extends TypeSubstitution(types)
{
   type T <: Term
   def +(other : Substitution)  : Substitution

//   private[silAST] def variables : Set[(BoundVariable,T)]

   def mapVariable(v : BoundVariable) : Option[T] //= varMap.get(v)
   protected[silAST] val varMap : Map[BoundVariable,T]
}

private[silAST] class SubstitutionC[TT<:Term](
                    types : Set[(TypeVariable,DataType)],
                    variables : Set[(BoundVariable,TT)]
                    ) extends Substitution(types)
{
  override type T = TT
  require (variables.forall((x)=>variables.count((y)=>y._1==x._1)==1))

  override def +(other : Substitution)  : Substitution =
    new SubstitutionC[Term](types ++ other.types,(varMap ++ other.varMap).toSet)

  protected[silAST] override val varMap : Map[BoundVariable,TT] = variables.toMap
  def mapVariable(v : BoundVariable) : Option[TT] = varMap.get(v)
}

trait PSubstitution extends Substitution
{
  override type T <: PTerm
  def mapVariable(v : BoundVariable) : Option[T]
  def +(other : PSubstitution)  : PSubstitution =
    new PSubstitutionC(types ++ other.types,varMap.toSet ++ other.varMap.toSet)
}

private[silAST] class PSubstitutionC(
    types : Set[(TypeVariable,DataType)],
    variables : Set[(BoundVariable,PTerm)]
  ) extends SubstitutionC(types,variables) with PSubstitution
{

}

trait DSubstitution extends Substitution
{
  override type T <: DTerm
  def mapVariable(v : BoundVariable) : Option[T]
  def +(other : DSubstitution)  : DSubstitution =
    new DSubstitutionC(types ++ other.types,varMap.toSet ++ other.varMap.toSet)
}

private[silAST] class DSubstitutionC(
                                      types : Set[(TypeVariable,DataType)],
                                      variables : Set[(BoundVariable,DTerm)]
                                      ) extends SubstitutionC(types,variables) with DSubstitution
{
}

class GSubstitution private[silAST](
                                           types : Set[(TypeVariable,DataType)],
                                           variables : Set[(BoundVariable,GTerm)]
                                           ) extends SubstitutionC[GTerm](types,variables)
                                              with PSubstitution with DSubstitution
{
  override type T = GTerm
  def +(other : GSubstitution)  : GSubstitution =
    new GSubstitution(types ++ other.types,variables ++ other.varMap.toSet)
}
