// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.utility

import viper.silver.parser._
import viper.silver.ast.utility.rewriter.StrategyBuilder

//? TODO: Considering copying metadata
//? TODO: Consider trafo to preserve original names for type checker errors
//? TODO: Consider refactoring to reuse fresh name calculator
//? TODO: Consider a stateful implementation of fresh name calculator to save time

object Sanitizer {

  def sanitizeBoundVariables(program: PProgram): PProgram = {

    def scope(node: PNode): Set[String] =
      NameAnalyser().namesInScope(program, Some(node))

    def fresh(name: String, scope: Set[String]): String = {
      var number = -1
      var freshName = name
      while (scope.contains(freshName)) {
        number += 1
        freshName = s"$name$$$number"
      }
      freshName
    }

    case class Context(renames: Map[String, String] = Map(), freshNames: Set[String] = Set())

    StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (forall: PForall, c) => {

        // Check if bound variables clash with scope
        val bounds = forall.vars.map(_.idndef.name).toSet
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

      case (PIdnDef(name), c) if c.renames.contains(name) =>
        (PIdnDef(c.renames(name)), c)

      case (PIdnUse(name), c) if c.renames.contains(name) =>
        (PIdnUse(c.renames(name)), c)

    }, Context()).execute(program)
  }
}
