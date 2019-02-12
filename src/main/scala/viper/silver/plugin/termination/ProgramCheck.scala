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

  val domains: mutable.ListMap[String, Domain] = collection.mutable.ListMap[String, Domain](program.domains.map(d => d.name -> d): _*)
  val fields: mutable.ListMap[String, Field] = collection.mutable.ListMap[String, Field](program.fields.map(f => f.name -> f): _*)
  val functions: mutable.ListMap[String, Function] = collection.mutable.ListMap[String, Function](program.functions.map(f => f.name -> f): _*)
  val predicates: mutable.ListMap[String, Predicate] = collection.mutable.ListMap[String, Predicate](program.predicates.map(f => f.name -> f): _*)
  val methods: mutable.ListMap[String, Method] = collection.mutable.ListMap[String, Method](program.methods.map(f => f.name -> f): _*)


  def clear(): Unit = {
    domains.clear()
      domains ++= program.domains.map(d => d.name -> d)
    fields.clear()
    fields ++= program.fields.map(f => f.name -> f)
    functions.clear
    functions ++= program.functions.map(f => f.name -> f)
    predicates.clear()
    predicates ++= program.predicates.map(f => f.name -> f)
    methods.clear()
    methods ++= program.methods.map(f => f.name -> f)
  }

  /**
    * Creates a new program with the needed fields added to it
    * @return a program
    */
  def createCheckProgram(): Program = {
    Program(domains.values.toSeq,
      fields.values.toSeq,
      functions.values.toSeq,
      predicates.values.toSeq,
      methods.values.toSeq)(program.pos, program.info, program.errT)
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

