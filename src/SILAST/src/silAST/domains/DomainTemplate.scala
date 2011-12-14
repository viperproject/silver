package silAST.domains

import silAST.ASTNode
import collection.Set
import collection.mutable.HashSet
import collection.immutable.HashMap
import silAST.symbols.logical.quantification.BoundVariable
import silAST.source.{noLocation, SourceLocation}
import silAST.types.{VariableType, DataType, DataTypeSequence, TypeVariable}
import silAST.expressions.terms.{GTerm, DTerm, PTerm, Term}


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
private [silAST] abstract class Substitution(
                                    types : Set[(TypeVariable,DataType)]
//                                    variables : collection.immutable.Set[(BoundVariable,Term)]
                                    ) extends TypeSubstitution(types)
{
//  protected val varMap = variables.toMap

  def mapVariable(v : BoundVariable) : Option[Term] //= varMap.get(v)
}

private[silAST] class SubstitutionC[+T<:Term](
                    types : Set[(TypeVariable,DataType)],
                    variables : collection.immutable.Set[(BoundVariable,T)]
                    ) extends Substitution(types)
{
  require (variables.forall((x)=>variables.count((y)=>y._1==x._1)==1))

  protected val varMap = variables.toMap
  def mapVariable(v : BoundVariable) : Option[T] = varMap.get(v)
}

private [silAST] trait PSubstitution
{
  def mapVariable(v : BoundVariable) : Option[PTerm]
}

private[silAST] class PSubstitutionC(
    types : Set[(TypeVariable,DataType)],
    variables : collection.immutable.Set[(BoundVariable,PTerm)]
  ) extends SubstitutionC(types,variables) with PSubstitution


private [silAST] trait DSubstitution
{
  def mapVariable(v : BoundVariable) : Option[DTerm]
}

private[silAST] class DSubstitutionC(
                                      types : Set[(TypeVariable,DataType)],
                                      variables : collection.immutable.Set[(BoundVariable,DTerm)]
                                      ) extends SubstitutionC(types,variables) with DSubstitution

private[silAST] class GSubstitution(
                                           types : Set[(TypeVariable,DataType)],
                                           variables : collection.immutable.Set[(BoundVariable,GTerm)]
                                           ) extends SubstitutionC[GTerm](types,variables)
                                              with PSubstitution with DSubstitution
{
}
