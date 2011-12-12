package silAST.domains

import silAST.ASTNode
import collection.Set
import collection.mutable.HashSet
import silAST.types.{NonReferenceDataType, DataType, DataTypeSequence, TypeVariable}
import silAST.source.{noLocation, SourceLocation}

abstract class Domain private[silAST](
                                    sl: SourceLocation
                                    ) extends ASTNode(sl)
{
  def getType : NonReferenceDataType

  def freeTypeVariables: Set[TypeVariable]

  def isCompatible(dataType: DataType): Boolean

  def getInstance(substitution: TypeSubstitution): Domain

  val name : String
  val functions: Set[DomainFunction]
  val predicates: Set[DomainPredicate]
  val axioms: Set[DomainAxiom]
  

}

final private[silAST] class DomainTemplateInstance(template : DomainTemplate,typeArguments:DataTypeSequence)
  extends Domain(typeArguments.sourceLocation)
{
  require (typeArguments.length == template.typeParameters.length)
  //TODO - ensure all type arguments are ground

  private val substitution = new TypeSubstitution((template.typeParameters.zip(typeArguments)).toSet)

  override val name : String = template.name + typeArguments.toString
  override val functions = for (ft <- template.functions) yield ft.substitute(substitution)
  override val predicates = for (pt <- template.predicates) yield pt.substitute(substitution)
  override val axioms = for (at <- template.axioms) yield at.substitute(substitution)

  def getType : NonReferenceDataType = new NonReferenceDataType(sourceLocation,this)

  def getInstance(s: TypeSubstitution): Domain = template.getInstance(typeArguments.substitute(s))
/*
  def isCompatible(d: Domain): Boolean =
    d match {
      case d : DomainTemplateInstance => template == d.template && typeArguments.isCompatible(d.typeArguments)
    }
  */

}
