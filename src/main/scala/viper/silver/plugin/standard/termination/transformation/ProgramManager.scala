// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.termination.transformation

import viper.silver.ast.{Domain, ExtensionMember, Field, Function, Method, Predicate, Program}
import viper.silver.verifier.AbstractError

import scala.collection.mutable

/**
  * A simple interface to transform/extend a program.
  * Contains utility functions to avoid name conflicts (e.g. when adding a new method)
  */
trait ProgramManager{

  // original program
  val program: Program

  // maps of all program features including the ones newly created/added
  protected val domains: mutable.Map[String, Domain] = collection.mutable.ListMap[String, Domain](program.domains.map(d => d.name -> d): _*)
  protected val fields: mutable.Map[String, Field] = collection.mutable.ListMap[String, Field](program.fields.map(f => f.name -> f): _*)
  protected val functions: mutable.Map[String, Function] = collection.mutable.ListMap[String, Function](program.functions.map(f => f.name -> f): _*)
  protected val predicates: mutable.Map[String, Predicate] = collection.mutable.ListMap[String, Predicate](program.predicates.map(f => f.name -> f): _*)
  protected val methods: mutable.Map[String, Method] = collection.mutable.ListMap[String, Method](program.methods.map(f => f.name -> f): _*)
  protected val extensions: mutable.Map[String, ExtensionMember] = collection.mutable.ListMap[String, ExtensionMember](program.extensions.map(e => e.name -> e): _*)

  /**
   * Creates a new program containing all the transformed and newly added features.
   * @return new program.
   */
  final def getNewProgram: Program = {
    Program(domains.values.toSeq,
      fields.values.toSeq,
      functions.values.toSeq,
      predicates.values.toSeq,
      methods.values.toSeq,
      extensions.values.toSeq)(program.pos, program.info, program.errT)
  }


  // all names used in the program
  // including arguments and local vars because they could also cause conflicts.
  private val usedNames: mutable.Set[String] = collection.mutable.Set(program.transitiveScopedDecls.map(_.name): _*)


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
}

trait ErrorReporter {
  // to report any errors occurring during transformation
  val reportError: AbstractError => Unit
}