package silAST.programs
{

import silAST.domains.DomainFactory
import collection.mutable.HashMap
import silAST.symbols.MethodFactory

class ProgramFactory(
    val name : String
  )
  {
    private val domainFactories = new HashMap[String,DomainFactory]
    def getDomainFactory(name : String) : DomainFactory =
      domainFactories.getOrElseUpdate(name, new DomainFactory(this,name))

    private val methodFactories = new HashMap[String,MethodFactory]
    def getMethodFactory(name : String) : MethodFactory =
      methodFactories.getOrElseUpdate(name,new MethodFactory(this,name))
  }
}


