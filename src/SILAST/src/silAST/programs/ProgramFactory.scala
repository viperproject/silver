package silAST.programs {

import silAST.source.SourceLocation
import silAST.types.{NonReferenceDataType, DataType}
import collection.mutable.{HashSet, HashMap}
import silAST.symbols._
import silAST.expressions._
import silAST.domains.{DomainPredicate, DomainFactory}
import silAST.expressions.util.{DTermSequence, PTermSequence, TermSequence}
import terms.{GeneralTerm, DomainTerm, Term, ProgramTerm}
import silAST.ASTNode

final class ProgramFactory(
                            val name: String
                            ) extends NodeFactory with ExpressionFactory{


  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  def getDomainFactory(name: String): DomainFactory =
    domainFactories.getOrElseUpdate(name, new DomainFactory(this, name))

  //////////////////////////////////////////////////////////////////////////
  def getMethodFactory(name: String): MethodFactory =
    methodFactories.getOrElseUpdate(name, new MethodFactory(this, name))

  //////////////////////////////////////////////////////////////////////////
  def defineDomainField(sl: SourceLocation, name: String, dataType: NonReferenceDataType): Field = {
    require(dataTypes.contains(dataType))
    defineField(new NonReferenceField(sl, name, dataType))
  }

  //////////////////////////////////////////////////////////////////////////
  def defineReferenceField(sl: SourceLocation, name: String): Field = {
    defineField(new ReferenceField(sl, name))
  }


  //////////////////////////////////////////////////////////////////////////
  //@Symbol construction
  //////////////////////////////////////////////////////////////////////////

  def defineField(field: Field): Field = {
    require(!fields.contains(field.name))

    fields += (field.name -> field)

    field
  }

  //////////////////////////////////////////////////////////////////////////
  def defineDataTypeSequence(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes.contains(_)))

    dataTypeSequences.getOrElseUpdate(types, new DataTypeSequence(types))
  }

  //////////////////////////////////////////////////////////////////////////
  def defineFunctionSignature(types: List[DataType]): DataTypeSequence = {
    require(types.forall(dataTypes.contains(_)))

    dataTypeSequences.getOrElseUpdate(types, new DataTypeSequence(types))
  }

  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////
  private val domainFactories = new HashMap[String, DomainFactory]
  private val methodFactories = new HashMap[String, MethodFactory]

  private val fields = new HashMap[String, Field]
  private val dataTypes = new HashSet[DataType]

  private val dataTypeSequences = new HashMap[List[DataType], DataTypeSequence]
}

}


