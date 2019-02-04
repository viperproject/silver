package viper.silver.plugin.termination

import viper.silver.ast._

import scala.collection.mutable

trait TerminationCheck{

  val program: Program
  val decreasesMap: Map[Function, DecreaseExp]

  // all names used in the program
  val usedNames: collection.mutable.Set[String] = collection.mutable.HashSet((
    program.functions
      ++ program.methods
      ++ program.fields
      ++ program.predicates
      ++ program.domains
      ++ program.domains.flatten(_.functions)
    ).map(_.name): _*)

  val decreasingFunc: Option[DomainFunc] = program.findDomainFunctionOptionally("decreasing")
  val boundedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("bounded")
  val nestedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("nested")
  val locationDomain: Option[Domain] =  program.domains.find(_.name == "Loc") // findDomainOptionally()?

  val neededLocalVars: mutable.ListMap[String, LocalVarDecl] = collection.mutable.ListMap[String, LocalVarDecl]()
  val neededFunctions: mutable.ListMap[String, Function] = collection.mutable.ListMap[String, Function]()
  val neededMethods: mutable.ListMap[String, Method] = collection.mutable.ListMap[String, Method]()
  val neededDomains: mutable.ListMap[String, Domain] = collection.mutable.ListMap[String, Domain]()

  def clear(): Unit = {
    neededLocalVars.clear()
    neededFunctions.clear()
    neededDomains.clear()
    neededMethods.clear()
  }

  def createCheckProgram(): Program


  /**
    * Creates a unique name for the program and adds it to the names already used in the program.
    * @param name which is wanted
    * @return a name which is unique in the program
    */
  def uniqueName(name: String): String = {
    var i = 1
    var newName = name
    while(usedNames.contains(newName)){
      newName = name + i
      i += 1
    }
    usedNames.add(newName)
    newName
  }


}

