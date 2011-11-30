package silAST.programs
{

import silAST.domains.DomainFactory
import collection.mutable.HashMap
import silAST.source.SourceLocation
import silAST.symbols.{NonReferenceField, ReferenceField, MethodFactory, Field}
import silAST.types.{NonReferenceDataType, DataType}

final class ProgramFactory(
    val name : String
  )
  {
    def getDomainFactory(name : String) : DomainFactory = null
      domainFactories.getOrElseUpdate(name, new DomainFactory(this,name))

    def getMethodFactory(name : String) : MethodFactory =
      methodFactories.getOrElseUpdate(name,new MethodFactory(this,name))

    def defineDomainField(sl : SourceLocation, name : String, dataType : NonReferenceDataType) : Field = {
      require(dataType.programFactory == this)
      defineField(new NonReferenceField(sl,name,dataType))
    }

    def defineReferenceField(sl : SourceLocation, name : String) : Field = {
      defineField(new ReferenceField(sl,name))
    }

    def defineField(field : Field) : Field = {
      require(!fields.contains(field.name))

      fields += (field.name -> field)

      field

    }

    private val domainFactories = new HashMap[String,DomainFactory]
    private val methodFactories = new HashMap[String,MethodFactory]

    private val fields = new HashMap[String,Field]
  }
}


