/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import scala.collection.mutable
import viper.silver.ast._

/** Utility methods for quantified permissions. */
object QuantifiedPermissions {
  object QPForall {
    def unapply(n: Forall): Option[(LocalVarDecl, /* Quantified variable */
                                    Exp, /* Condition */
                                    Exp, /* Receiver e of acc(e.f, p) */
                                    Field, /* Field f of acc(e.f, p) */
                                    Exp, /* Permissions p of acc(e.f, p) */
                                    Forall, /* AST node of the forall (for error reporting) */
                                    FieldAccess)] = /* AST node for e.f (for error reporting) */

      n match {
        case forall@Forall(Seq(lvd @ LocalVarDecl(_, _ /*ast.types.Ref*/)),
                           triggers,
                           Implies(condition, FieldAccessPredicate(fa@FieldAccess(rcvr, f), gain)))
          if     rcvr.exists(_ == lvd.localVar)
              && triggers.isEmpty =>

          Some((lvd, condition, rcvr, f, gain, forall, fa))

        case _ => None
      }
  }

  def quantifiedFields(root: Node, program: Program): collection.Set[Field] = {
    val collected = mutable.LinkedHashSet[Field]()
    val visited = mutable.Set[Member]()
    val toVisit = mutable.Queue[Member]()

    root match {
      case m: Member => toVisit += m
      case _ =>
    }

    toVisit ++= Nodes.referencedMembers(root, program)

    quantifiedFields(toVisit, collected, visited, program)

    collected
  }

  private def quantifiedFields(toVisit: mutable.Queue[Member],
                               collected: mutable.LinkedHashSet[Field],
                               visited: mutable.Set[Member],
                               program: Program) {

    while (toVisit.nonEmpty) {
      val root = toVisit.dequeue()

      root visit {
        case QPForall(_, _, _, field, _, _, _) => collected += field
      }

      visited += root

      utility.Nodes.referencedMembers(root, program) foreach (m =>
        if (!visited.contains(m)) toVisit += m)
    }
  }
}
