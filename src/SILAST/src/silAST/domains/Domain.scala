package silAST.domains

import silAST.ASTNode
import collection.Set
import collection.mutable.HashSet
import collection.mutable.HashMap
import silAST.types._
import silAST.source.{noLocation, SourceLocation}


abstract class Domain private[silAST] extends ASTNode
{
  override lazy val toString = "domain " + name +
    "{\n" +
    (if (!functions.isEmpty) functions.mkString("\t", "\n\t", "\n") else "") +
    (if (!predicates.isEmpty) predicates.mkString("\t", "\n\t", "\n") else "") +
    (if (!axioms.isEmpty) axioms.mkString("\t", "\n\t", "\n") else "") +
    "}"

  def name : String
  def fullName : String

  def functions: Set[DomainFunction]
  def predicates: Set[DomainPredicate]
  def axioms: Set[DomainAxiom]

  def getType : DataType

  def freeTypeVariables: Set[TypeVariable]
  def isCompatible(other : Domain) : Boolean

  def substitute(ts : TypeVariableSubstitution): Domain

  override def equals(other : Any) : Boolean = {
    other match{
      case d : Domain => d eq this
      case _ => false
    }
  }
  override def hashCode() : Int = fullName.hashCode()
}

////////////////////////////////////////////////////////////////////////
private[silAST] class DomainC(
          val sourceLocation : SourceLocation,
          val name: String,
          typeVariableNames : Seq[(SourceLocation, String)]
    ) extends Domain
{
  //No duplicate type variable name
  require(typeVariableNames.forall((s)=>typeVariableNames.count(_._2==s._2)==1))

  override def fullName : String =
    name + (if (typeParameters.length==0) "" else typeParameters.mkString("[",",","]"))
  val typeParameters : Seq[TypeVariable] = for (n <- typeVariableNames) yield new TypeVariable(n._1,n._2,this)
  val freeTypeVariables = typeParameters.toSet

  def functions: Set[DomainFunction] = pFunctions
  def predicates: Set[DomainPredicate] = pPredicates
  def axioms: Set[DomainAxiom] = pAxioms

  private[silAST] val pFunctions = new HashSet[DomainFunction]
  private[silAST] val pPredicates = new HashSet[DomainPredicate]
  private[silAST] val pAxioms = new HashSet[DomainAxiom]

  val pInstances = new HashMap[DataTypeSequence,Domain]

  def getInstance(typeArguments: DataTypeSequence): Domain = {
    require (typeArguments.length == typeParameters.length)
    if (typeArguments.isEmpty)
      this
    else
      pInstances.getOrElseUpdate(typeArguments, new DomainInstance(typeArguments.sourceLocation,this,typeArguments))
  }

  def substitute(s:TypeVariableSubstitution): Domain = {
    val typeArguments = new DataTypeSequence((for (t<-typeParameters) yield s.mapType(t,new VariableType(t.sourceLocation,t))))
    getInstance(typeArguments)
  }

  //Maybe relax a bit
  def isCompatible(other:Domain) : Boolean = other==this

  def getType : NonReferenceDataType = new NonReferenceDataType(sourceLocation,this)
}


private[silAST] final class DomainInstance(
  val sourceLocation : SourceLocation,
  val original : DomainC,
  val typeArguments:DataTypeSequence  )
  extends Domain
{
  protected[silAST] def typeHeaderString : String = ""

  override def fullName : String = name
  val name : String = original.name + typeArguments.toString
  val substitution = new TypeSubstitutionC(original.typeParameters.zip(typeArguments).toSet, Set(), noLocation, this)

  val getType : NonReferenceDataType = new NonReferenceDataType(sourceLocation,this)

  override lazy val functions = for (f <- original.functions) yield f.substitute(substitution)
  override lazy val predicates = (for (p <- original.predicates) yield p.substitute(substitution)).toSet
  override lazy val axioms = (for (a <- original.axioms) yield a.substitute(substitution)).toSet

  override val freeTypeVariables = typeArguments.freeTypeVariables.toSet

  def substitute(s: TypeVariableSubstitution): Domain = original.getInstance(typeArguments.substitute(s))

  def isCompatible(other:Domain) : Boolean =
    other match {
      case d : DomainInstance => d.original==original && typeArguments.isCompatible(d.typeArguments)
      case _ => false
    }

  override def equals(other : Any) : Boolean =
  {
    other match{
      case d : Domain => d eq this
      case _ => false
    }
  }

  override def hashCode() : Int = fullName.hashCode()
}
