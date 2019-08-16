// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import viper.silver.ast.utility.rewriter._
import viper.silver.ast.utility.Expressions
import viper.silver.parser._
import viper.silver.ast._

import scala.language.postfixOps

//? TODO: Considering copying metadata
//? TODO: Consider trafo to preserve original names for type checker errors
//? TODO: Consider refactoring to reuse fresh name calculator
//? TODO: Consider a stateful implementation of fresh name calculator to save time

object Sanitizer {

  private def fresh(name: String, scope: Set[String]): String = {
    var number = -1
    var freshName = name
    while (scope.contains(freshName)) {
      number += 1
      freshName = s"$name$$$number"
    }
    freshName
  }

  // This method renames bound variables when their identifiers already exist in the same scope,
  // therefore preventing clashes with other entities and preventing free variables to be
  // 'captured', i.e. mistakenly considered quantified variables.
  def sanitizeBoundVariables(program: PProgram): PProgram = {

    def scopeAt(node: PNode): Set[String] =
      NameAnalyser().namesInScope(program, Some(node))

    case class Context(renames: Map[String, String] = Map(), freshNames: Set[String] = Set())

    StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (forall: PForall, c) => {

        // Check if bound variables clash with scope
        val bounds = forall.vars.map(_.idndef.name).toSet
        val scope = scopeAt(forall)
        val intersection = scope & bounds

        // Define how clashing variables will be renamed to fresh names
        var renames = c.renames
        var freshNames = c.freshNames

        intersection.foreach {
          name =>
            val freshName = fresh(name, scope ++ bounds ++ freshNames)
            renames += ((name, freshName))
            freshNames += freshName
        }

        (forall, Context(renames, freshNames))
      }

      case (PIdnDef(name), c) if c.renames.contains(name) =>
        (PIdnDef(c.renames(name)), c)

      case (PIdnUse(name), c) if c.renames.contains(name) =>
        (PIdnUse(c.renames(name)), c)

    }, Context()).execute(program)
  }

  def replaceFreeVariablesInExpression[E <: Exp](expression: E, replaces: Map[LocalVar, Exp]): E = {

    def scopeAt(node: Node): Set[String] = {
      //Set("Test") //? // TODO: get scope
      val result = node match {
        case scope: Scope => scope.transitiveScopedDecls.map(_.name).toSet
      }

      result //? Remove
    }

    def freeVariables(exp: Exp): Set[String] = {
      Expressions.freeVariables(exp).map(_.name)
    }

    // Free variables introduced by replacement
    val introducedFreeVariables = replaces.values.flatMap(freeVariables(_)).toSet
    // TODO: check if will actually be introduced, because not all replacements should occur

    case class Context(replaces: Map[LocalVar, Exp], renames: Map[String, String] = Map(), freshNames: Set[String] = Set())

    val result = StrategyBuilder.RewriteNodeAndContext[Node, Context]({
      case (forall: Forall, c) => {

        // Check if bound variables clash with scope
        val scope = scopeAt(forall) | introducedFreeVariables
        val bounds = forall.variables.map(_.name).toSet
        val intersection = scope & bounds

        var renames = c.renames
        var freshNames = c.freshNames

        // Define how clashing bound variables will be renamed to fresh names
        intersection.foreach {
          name =>
            val freshName = fresh(name, scope ++ bounds ++ freshNames)
            renames += ((name, freshName))
            freshNames += freshName
        }

        assert((renames.keys.toSet & c.replaces.keys.map(_.name).toSet).isEmpty)

        (forall, c.copy(renames = renames, freshNames = freshNames))
      }

      case (lv: LocalVarDecl, c) if c.renames.contains(lv.name) =>
        (LocalVarDecl(c.renames(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      case (lv: LocalVar, c) if c.renames.contains(lv.name) =>
        (LocalVar(c.renames(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      case (lv: LocalVar, c) if c.replaces.contains(lv) =>
        (c.replaces(lv), c.copy(replaces = Map()))

    }, Context(replaces)).execute(expression).asInstanceOf[E] //? remove cast

    result //?
  }

  def sanitizedReplacement2[E <: Exp](expression: E, variables: Seq[LocalVarDecl], values: Seq[Exp]): E = {

    def scope(node: Node): Set[String] =
      Set("Test") //? // TODO: get scope

    case class Context(renames: Map[String, String] = Map(), freshNames: Set[String] = Set())

    StrategyBuilder.RewriteNodeAndContext[Node, Context]({
      case (forall: Forall, c) => {

        // Check if bound variables clash with scope
        val bounds = forall.variables.map(_.name).toSet
        val intersection = scope(forall) & bounds

        // Define how clashing variables will be renamed to fresh names
        var renames = c.renames
        var freshNames = c.freshNames

        intersection.foreach {
          name =>
            val freshName = fresh(name, scope(forall) ++ bounds ++ freshNames)
            renames += ((name, freshName))
            freshNames += freshName
        }

        (forall, Context(renames, freshNames))
      }

      case (lv: LocalVarDecl, c) if c.renames.contains(lv.name) =>
        (LocalVarDecl(c.renames(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

      case (lv: LocalVar, c) if c.renames.contains(lv.name) =>
        (LocalVar(c.renames(lv.name), lv.typ)(lv.pos, lv.info, lv.errT), c)

    }, Context()).execute(expression)
  }
  // This method replaces free variables in the expression by their corresponding values. If bound variables
  // exist in the expression and their identifiers clash with new variables in values, then the corresponding
  // bound variables are renamed prior to the replacement, preventing the new free variables to be 'captured'.
  // This method assumes that 'sanitizeBoundVariables' was executed previously.
  def instantiateVariables[A <: Exp](expression: A, variables: Seq[LocalVarDecl], values: Seq[Exp]): A = {
    assert(variables.size == values.size, "The number of variables and values must match")

    val bounds = expression.deepCollect {
      //? case fa: Forall => fa.variables
      case dec: LocalVarDecl => dec.name
    } toSet

    val image = values.flatMap {
      value =>
        value.deepCollect {
          case dec: LocalVarDecl => dec.name
          case use: LocalVar => use.name
        }
    } toSet

    val intersection = bounds & image
    var renames = Map.empty[String, String]
    val replaces = variables map(_.localVar) zip values toMap

    intersection.foreach {
      name =>
        // TODO: Add scope to names to be avoided
        renames += ((name, fresh(name, bounds ++ image ++ renames.keys)))
    }

    // Sanitize expression prior to replacement
    val renamed = StrategyBuilder.Slim[Node]({
      // TODO: Copy metadata
      case dec: LocalVarDecl if renames.contains(dec.name) => dec.copy(name = renames(dec.name))(dec.pos, dec.info, dec.errT)
      case use: LocalVar if renames.contains(use.name) => use.copy(name = renames(use.name))(use.pos, use.info, use.errT)
    }).execute(expression)

    // Replace variables by values
    StrategyBuilder.Slim[Node]({
      // TODO: Copy metadata
      case use: LocalVar if replaces.contains(use) => replaces(use)
    }).execute(renamed)
  }
}
