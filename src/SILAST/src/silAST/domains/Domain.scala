package silAST.domains

import silAST.ASTNode
import silAST.source.SourceLocation
import collection.Set
import collection.mutable.HashSet
import silAST.types.TypeVariable

class Domain private[silAST](
                                    sl: SourceLocation,
                                    val name: String,
                                    typeVariableNames :Seq[(SourceLocation,String)]
                                    ) extends ASTNode(sl)
{
  require(typeVariableNames.forall((s)=>typeVariableNames.count(_._2==s._2)==1))
  
  val typeParameters : Seq[TypeVariable] = for (n <- typeVariableNames) yield new TypeVariable(n._1,this,n._2)
  private[silAST] val pFunctions = new HashSet[DomainFunction]
  private[silAST] val pPredicates = new HashSet[DomainPredicate]
  private[silAST] val pAxioms = new HashSet[DomainAxiom]

  def functions: Set[DomainFunction] = pFunctions
  def predicates: Set[DomainPredicate] = pPredicates
  def axioms: Set[DomainAxiom] = pAxioms


  override def toString = "domain " + name + typeParameters.mkString("[",",","]") + "{\n" +
    (if (!functions.isEmpty) functions.mkString("\t", "\n\t", "\n") else "") +
    (if (!predicates.isEmpty) predicates.mkString("\t", "\n\t", "\n") else "") +
    (if (!axioms.isEmpty) axioms.mkString("\t", "\n\t", "\n") else "") +
    "}"

  override def subNodes = functions.toList ++ predicates.toList ++ axioms.toList
}