// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.trafo.util

import viper.silver.ast._
import viper.silver.verifier.AbstractError

import scala.collection.mutable

/**
  * An interface to transform a program (e.g. a program including check methods).
  * Contains utility functions to avoid name conflicts (e.g. when adding a new domain)
  */
trait ProgramManager{

  // original program
  val program: Program

  // to report any errors occurring during transformation
  val reportError: AbstractError => Unit

  // maps of all program features including the ones newly created/added
  protected val domains: mutable.ListMap[String, Domain] = collection.mutable.ListMap[String, Domain](program.domains.map(d => d.name -> d): _*)
  protected val fields: mutable.ListMap[String, Field] = collection.mutable.ListMap[String, Field](program.fields.map(f => f.name -> f): _*)
  protected val functions: mutable.ListMap[String, Function] = collection.mutable.ListMap[String, Function](program.functions.map(f => f.name -> f): _*)
  protected val predicates: mutable.ListMap[String, Predicate] = collection.mutable.ListMap[String, Predicate](program.predicates.map(f => f.name -> f): _*)
  protected val methods: mutable.ListMap[String, Method] = collection.mutable.ListMap[String, Method](program.methods.map(f => f.name -> f): _*)

  // all names used in the program
  private val usedNames: mutable.Set[String] = collection.mutable.HashSet((
    program.functions
      ++ program.methods
      ++ program.fields
      ++ program.predicates
      ++ program.domains
      ++ program.domains.flatten(_.functions)
    ).map(_.name): _*)


  /**
    * Checks if a name already occurs in the program.
    * @param name to be checked
    * @return true iff the name is used in the program.
    */
  def containsName(name: String): Boolean = {
    usedNames.contains(name)
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
    while(containsName(newName)){
      newName = name + i
      i += 1
    }
    usedNames.add(newName)
    newName
  }

  /**
    * Cached program for the gerNetProgram call.
    */
  private var newProgram: Option[Program] = None

  /**
    * @return the new program containing all the added checks.
    */
  final def getCheckProgram: Program = {
    if(newProgram.isEmpty){
      newProgram = Some(generateCheckProgram())
    }
    newProgram.get
  }

  /**
    * Creates a new program with the additional features.
    * Should only be called once.
    * @return new program.
    */
  protected def generateCheckProgram(): Program = {
    Program(domains.values.toSeq,
      fields.values.toSeq,
      functions.values.toSeq,
      predicates.values.toSeq,
      methods.values.toSeq, Seq())(program.pos, program.info, program.errT)
  }
}
