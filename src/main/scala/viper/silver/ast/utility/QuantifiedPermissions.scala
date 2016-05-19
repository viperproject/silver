/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import scala.collection.mutable
import viper.silver.ast._

/** Utility methods for quantified predicate permissions. */
object QuantifiedPermissions {
  object QPPForall {
    //TODO
    def unapply(n: Forall): Option[(LocalVarDecl, /* Quantified variable */
      Exp, /* Condition */
      Seq[Exp], /* Predicate arguments in acc(pred(args), p) */
      String, /* predicate name of acc(pred(args), p) */
      Exp, /* Permissions p of acc(e.f, p) */
      Forall, /* AST node of the forall (for error reporting) */
      PredicateAccessPredicate)] = /* AST node for e.f (for error reporting) */

      n match {
        case forall@Forall(Seq(lvd @ LocalVarDecl(_, _ /*Ref*/)),
        triggers,
        Implies(condition, pa@PredicateAccessPredicate(PredicateAccess(args, predname), gain)))
          //TODO predicate exists check?
          if    triggers.isEmpty =>

          Some((lvd, condition, args, predname, gain, forall, pa))

        case _ => None
      }

  }

  /** Utility methods for quantified field permissions. */
  object QPForall {
    def unapply(n: Forall): Option[(LocalVarDecl, /* Quantified variable */
                                    Exp, /* Condition */
                                    Exp, /* Receiver e of acc(e.f, p) */
                                    Field, /* Field f of acc(e.f, p) */
                                    Exp, /* Permissions p of acc(e.f, p) */
                                    Forall, /* AST node of the forall (for error reporting) */
                                    FieldAccess)] = /* AST node for e.f (for error reporting) */

      n match {
        case forall@Forall(Seq(lvd @ LocalVarDecl(_, _ /*Ref*/)),
                           triggers,
                           Implies(condition, FieldAccessPredicate(fa@FieldAccess(rcvr, f), gain)))
          if     rcvr.exists(_ == lvd.localVar)
              && triggers.isEmpty =>

          Some((lvd, condition, rcvr, f, gain, forall, fa))

        case _ => None
      }
  }

  /* TODO: Computing the set of quantified fields would probably benefit from caching
   *       the (sub)results per member. Ideally, it would be possible to retrieve the
   *       (cached) results from the members themselves,
   *       e.g. someMethod.quantifiedFields.
   */

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
