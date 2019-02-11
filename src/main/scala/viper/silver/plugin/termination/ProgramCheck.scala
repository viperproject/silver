package viper.silver.plugin.termination

import viper.silver.ast._

import scala.collection.mutable

/**
  * An interface which offers multiple classes to add additional code to a program
  * without causing name conflicts.
  */
trait ProgramCheck{

  val program: Program

  // all names used in the program
  val usedNames: collection.mutable.Set[String] = collection.mutable.HashSet((
    program.functions
      ++ program.methods
      ++ program.fields
      ++ program.predicates
      ++ program.domains
      ++ program.domains.flatten(_.functions)
    ).map(_.name): _*)

  val neededDomains: mutable.ListMap[String, Domain] = collection.mutable.ListMap[String, Domain]()
  val neededFields: mutable.ListMap[String, Field] = collection.mutable.ListMap[String, Field]()
  val neededFunctions: mutable.ListMap[String, Function] = collection.mutable.ListMap[String, Function]()
  val neededPredicates: mutable.ListMap[String, Predicate] = collection.mutable.ListMap[String, Predicate]()
  val neededMethods: mutable.ListMap[String, Method] = collection.mutable.ListMap[String, Method]()


  def clear(): Unit = {
    neededDomains.clear()
    neededFields.clear()
    neededFunctions.clear()
    neededPredicates.clear()
    neededMethods.clear()
  }

  /**
    * Creates a new program with the needed fields added to it
    * @return a program
    */
  def createCheckProgram(): Program = {
    Program(program.domains ++ neededDomains.values,
      program.fields ++ neededFields.values,
      program.functions ++ neededFunctions.values,
      program.predicates ++ neededPredicates.values,
      program.methods ++ neededMethods.values)(program.pos, program.info, program.errT)
  }


  /**
    * Creates a unique name for the program and adds it to the names already used in the program.
    * Should be used whenever a field, method, predicate, etc. is added to the needed fields.
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

