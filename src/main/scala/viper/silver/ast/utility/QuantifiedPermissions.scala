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


    object QuantifiedPermission {
      def unapply(n:Forall):
      Option[(LocalVarDecl,
        Exp,
        Exp)] =
        n match {
          case forall@Forall(Seq(lvd @ LocalVarDecl(_, _ /*Ref*/)),
          triggers,
          Implies(condition, expr)) =>
            Some((lvd, condition,expr))
          //case were no condition is deifned
          case forall@Forall(Seq(lvd@LocalVarDecl(_, _)), triggers, expr) =>
            Some(lvd, BoolLit(true)(forall.pos, forall.info), expr)
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
              /*&& triggers.isEmpty*/ =>

            Some((lvd, condition, rcvr, f, gain, forall, fa))
          case forall@Forall(Seq(lvd@LocalVarDecl(_, _)), triggers, FieldAccessPredicate(fa@FieldAccess(rcvr, f), gain))
            if rcvr.exists(_ == lvd.localVar) =>
            Some((lvd, BoolLit(true)(forall.pos, forall.info), rcvr, f, gain, forall, fa))
          case _ => None
        }
    }



    object QPPForall {
      def unapply(n: Forall): Option[(LocalVarDecl, /* Quantified variable */
        Exp, /* Condition */
        Seq[Exp], /* Predicate arguments in acc(pred(args), p) */
        String, /* predicate name of acc(pred(args), p) */
        Exp, /* Permissions p of acc(e.f, p) */
        Forall, /* AST node of the forall (for error reporting) */
        PredicateAccessPredicate)] = /* AST node for e.f (for error reporting) */

        n match {
          case forall@Forall(Seq(lvd@LocalVarDecl(_, _ /*Ref*/)),
          triggers,
          Implies(condition, pa@PredicateAccessPredicate(PredicateAccess(args, predname), gain))) =>
            Some((lvd, condition, args, predname, gain, forall, pa))
          case forall@Forall(Seq(lvd@LocalVarDecl(_, _)), triggers, pa@PredicateAccessPredicate(PredicateAccess(args, predname), gain)) =>
            Some((lvd, BoolLit(true)(forall.pos, forall.info), args, predname, gain, forall, pa))
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

  /* TODO: Computing the set of quantified predicates would probably benefit from caching
 *       the (sub)results per member. Ideally, it would be possible to retrieve the
 *       (cached) results from the members themselves,
 *       e.g. someMethod.quantifiedFields.
 */

  def quantifiedPredicates(root: Node, program: Program): collection.Set[Predicate] = {
    val collected = mutable.LinkedHashSet[Predicate]()
    val visited = mutable.Set[Member]()
    val toVisit = mutable.Queue[Member]()

    root match {
      case m: Member => toVisit += m
      case _ =>
    }

    toVisit ++= Nodes.referencedMembers(root, program)

    quantifiedPredicates(toVisit, collected, visited, program)

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

  private def quantifiedPredicates(toVisit: mutable.Queue[Member],
                               collected: mutable.LinkedHashSet[Predicate],
                               visited: mutable.Set[Member],
                               program: Program) {

    while (toVisit.nonEmpty) {
      val root = toVisit.dequeue()

      root visit {
        case QPPForall(_, _, _,predname , _, _, _) => collected += program.findPredicate(predname)
      }

      visited += root

      utility.Nodes.referencedMembers(root, program) foreach (m =>
        if (!visited.contains(m)) toVisit += m)
    }
  }

  def rewriteForall (e: Forall) : Exp = {
    val vars = e.variables
    val triggers = e.triggers
    e match {
      case qp@QuantifiedPermission (v, cond, expr) =>
        val stmts:Exp = expr match {
          case AccessPredicate (_, _) =>
            e
          case and@And (e0, e1) =>
            val rewrittenExp = And(rewriteForall (Forall (vars, triggers, Implies (cond, e0) (expr.pos, expr.info) ) (e.pos, e.info)),
              rewriteForall (Forall (vars, triggers, Implies (cond, e1) (expr.pos, expr.info) ) (e.pos, e.info))) (and.pos, and.info)
            rewrittenExp
          //combination: implies
          case implies@Implies (e0, e1) =>
            //e0 must be pure
            val newCond = And (cond, e0) (cond.pos, cond.info)
            val newFa = Forall (vars, triggers, Implies (newCond, e1) (expr.pos, expr.info) ) (e.pos, e.info)
            val rewrittenExp:Exp = rewriteForall (newFa)
            rewrittenExp
          case _ =>
            e
        }
        stmts
      case _ =>
        e
    }
  }
}
