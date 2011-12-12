package silAST.domains

import silAST.ASTNode
import collection.Set
import collection.mutable.HashSet
import collection.immutable.HashMap
import silAST.symbols.logical.quantification.BoundVariable
import silAST.expressions.terms.Term
import silAST.source.{noLocation, SourceLocation}
import silAST.types.{VariableType, DataType, DataTypeSequence, TypeVariable}

class DomainTemplate private[silAST](
                                    sl: SourceLocation,
                                    val name: String,
                                    typeVariableNames :Seq[(SourceLocation,String)]
                                    ) extends ASTNode(sl)
{
  val pInstances = new HashMap[DataTypeSequence,Domain]
  def instances : Set[Domain] = pInstances.values.toSet

  def getInstance(typeArguments: DataTypeSequence): Domain =
    pInstances.getOrElse(typeArguments,new DomainTemplateInstance(this,typeArguments))


  val typeParameters : Seq[TypeVariable] = for (n <- typeVariableNames) yield new TypeVariable(n._1,this,n._2)

  def functions: Set[DomainFunction] = pFunctions
  def predicates: Set[DomainPredicate] = pPredicates
  def axioms: Set[DomainAxiom] = pAxioms

  override def toString = "domain " + name + typeParameters.mkString("[",",","]") + "{\n" +
    (if (!functions.isEmpty) functions.mkString("\t", "\n\t", "\n") else "") +
    (if (!predicates.isEmpty) predicates.mkString("\t", "\n\t", "\n") else "") +
    (if (!axioms.isEmpty) axioms.mkString("\t", "\n\t", "\n") else "") +
    "}"

  override def subNodes = functions.toList ++ predicates.toList ++ axioms.toList

  require(typeVariableNames.forall((s)=>typeVariableNames.count(_._2==s._2)==1))

  private[silAST] val pFunctions = new HashSet[DomainFunction]
  private[silAST] val pPredicates = new HashSet[DomainPredicate]
  private[silAST] val pAxioms = new HashSet[DomainAxiom]
  
  val domain = new DomainTemplateInstance(this,DataTypeSequence((for (t<-typeParameters) yield new VariableType(t.sourceLocation,t)) : _*))
}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
private [silAST] class TypeSubstitution(private val types : Set[(TypeVariable,DataType)],val sourceLocation : SourceLocation = noLocation)
{
  val typeVariables : Set[TypeVariable] = for (t <- types) yield t._1

  protected val typeMap = types.toMap
  def mapType    (v : TypeVariable, t : DataType) : DataType = typeMap.getOrElse(v,t)

}

///////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////
private [silAST] class Substitution[+T <: Term](
                                    types : Set[(TypeVariable,DataType)],
                                    val variables : Set[(BoundVariable,T)]
                                    ) extends TypeSubstitution(types)
{
  protected val varMap = variables.toMap

  def mapVariable(v : BoundVariable,t : T       ) : T        = varMap .getOrElse(v,t)
}