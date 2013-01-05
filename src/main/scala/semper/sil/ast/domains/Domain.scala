package semper.sil.ast.domains

import semper.sil.ast.ASTNode
import collection.{mutable, Set}
import semper.sil.ast.types._
import semper.sil.ast.source.SourceLocation


////////////////////////////////////////////////////////////////////////
trait GDomain extends ASTNode {
  override def toString = "domain " + fullName +
    "{\n" +
    (if (!functions.isEmpty) functions.mkString("\t", "\n\t", "\n") else "") +
    (if (!predicates.isEmpty) predicates.mkString("\t", "\n\t", "\n") else "") +
    (if (!axioms.isEmpty) axioms.mkString("\t", "\n\t", "\n") else "") +
    "}"

  def name: String

  def fullName: String

  def freeTypeVariables: collection.immutable.Set[TypeVariable]

  def substitute(ts: TypeVariableSubstitution): Domain

  def functions: collection.Set[DomainFunction]

  def predicates: collection.Set[DomainPredicate]

  def axioms: collection.Set[DomainAxiom]

  def getType: DataType

  def isCompatible(other: Domain): Boolean

  override def equals(other: Any): Boolean = {
    other match {
      case d: GDomain => d eq this
      case _ => false
    }
  }

  override def hashCode(): Int = fullName.hashCode()
}

////////////////////////////////////////////////////////////////////////
trait Domain extends GDomain {
}

////////////////////////////////////////////////////////////////////////
trait DomainTemplate extends GDomain {
  def typeParameters: Seq[TypeVariable]

  def getInstance(typeArguments: DataTypeSequence): DomainInstance

  def instances: Set[Domain]

  def domain: Domain
}

////////////////////////////////////////////////////////////////////////
private[sil] class DomainTemplateC(
                                    val name: String,
                                    typeVariableNames: Seq[(SourceLocation, String, List[String])]
                                    )
                                  (val sourceLocation: SourceLocation, override val comment: List[String])
  extends DomainTemplate {
  //No duplicate type variable name
  require(typeVariableNames.forall((s) => typeVariableNames.count(_._2 == s._2) == 1))

  def fullName: String =
    name + typeParameters.mkString("[", ",", "]")

  val typeParameters: Seq[TypeVariable] = for (n <- typeVariableNames) yield new TypeVariable(n._2, this)(n._1, n._3)
  val freeTypeVariables = typeParameters.toSet

  def functions: Set[DomainFunction] = pFunctions

  def predicates: Set[DomainPredicate] = pPredicates

  def axioms: Set[DomainAxiom] = pAxioms

  private[sil] val pFunctions = new mutable.HashSet[DomainFunction]
  private[sil] val pPredicates = new mutable.HashSet[DomainPredicate]
  private[sil] val pAxioms = new mutable.HashSet[DomainAxiom]

  override def instances: Set[Domain] = pInstances.values.toSet

  override lazy val domain: Domain = getInstance(DataTypeSequence((for (t <- typeParameters) yield VariableType(t)(t.sourceLocation, t.comment)): _*))
  private[sil] lazy val dataType = NonReferenceDataType(domain)(domain.sourceLocation, domain.comment)

  override def getType = dataType

  val pInstances = new mutable.HashMap[DataTypeSequence, DomainInstance]

  def getInstance(typeArguments: DataTypeSequence): DomainInstance = {
    require(typeArguments.length == typeParameters.length)
    //    if (typeArguments.isEmpty)
    //      this
    //    else
    pInstances.getOrElseUpdate(typeArguments, new DomainInstance(this, typeArguments)(typeArguments.sourceLocation))
  }

  def substitute(s: TypeVariableSubstitution): Domain = {
    val typeArguments = new DataTypeSequence((for (t <- typeParameters) yield s.mapType(t, new VariableType(t)(t.sourceLocation, t.comment))))
    getInstance(typeArguments)
  }

  //Maybe relax a bit
  def isCompatible(other: Domain): Boolean = other == this

  //  def getType : NonReferenceDataType = new NonReferenceDataType(this)(sourceLocation)
}

////////////////////////////////////////////////////////////////////////
private[sil] final class DomainInstance(
                                         val template: DomainTemplate,
                                         val typeArguments: DataTypeSequence
                                         )
                                       (val sourceLocation: SourceLocation)
  extends Domain {
  protected[sil] def typeHeaderString: String = ""

  override val comment = Nil

  override def fullName: String = name

  val name: String = template.name + (if (typeArguments.isEmpty) "" else typeArguments.toString)
  val substitution = new TypeSubstitutionC(template.typeParameters.zip(typeArguments).toSet, Set())

  val getType: NonReferenceDataType = new NonReferenceDataType(this)(sourceLocation, comment)

  def substitute(s: TypeVariableSubstitution): Domain = template.getInstance(typeArguments.substitute(s))

  override val freeTypeVariables = typeArguments.freeTypeVariables.toSet

  def isCompatible(other: Domain): Boolean =
    other match {
      case d: DomainInstance => d.template == template && typeArguments.isCompatible(d.typeArguments)
      case _ => false
    }

  override def equals(other: Any): Boolean = {
    other match {
      case d: Domain => d eq this
      case _ => false
    }
  }

  override def hashCode(): Int = fullName.hashCode()

  override lazy val functions = for (f <- template.functions) yield f.substituteI(substitution)
  override lazy val predicates = (for (p <- template.predicates) yield p.substituteI(substitution)).toSet
  override lazy val axioms = (for (a <- template.axioms) yield a.substitute(substitution)).toSet
}
