// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import scala.reflect.ClassTag
import scala.collection.immutable.ListSet

abstract class GenericAxiomRewriter[Type <: AnyRef,
                                    Exp <: AnyRef : ClassTag,
                                    Var <: Exp : ClassTag,
                                    Quantification <: Exp : ClassTag,
                                    Eq <: Exp,
                                    And <: Exp,
                                    Implies <: Exp,
                                    Plus <: Exp,
                                    Minus <: Exp,
                                    Trigger <: AnyRef/*,
                                    ForbiddenInTrigger <: GenericTriggerGenerator.ForbiddenInTrigger[Type] with Exp : ClassTag*/] {

  type TriggerSet = GenericTriggerGenerator.TriggerSet[Exp]
  val TriggerSet = GenericTriggerGenerator.TriggerSet[Exp] _

  type ForbiddenInTrigger = Exp

  /*
   * Abstract members - type arguments
   */

  protected def Exp_type(exp: Exp): Type
  protected def Exp_shallowCollect[R](node: Exp)(f: PartialFunction[Exp, R]): Seq[R]
  protected def Exp_contains(node: Exp, other: Exp): Boolean
  protected def Exp_replace(node: Exp, original: Exp, replacement: Exp): Exp

  protected def Eq(e1: Exp, e2: Exp): Exp
  protected def And(es: Seq[Exp]): Exp
  protected def Implies(e1: Exp, e2: Exp): Exp

  protected def Var_id(v: Var): String

  protected def Quantification_vars(q: Quantification): Seq[Var]
  protected def Quantification_body(q: Quantification): Exp
  protected def Quantification_copy(q: Quantification, vars: Seq[Var], body: Exp, triggers: Seq[Trigger]): Quantification

  protected def Trigger_exps(t: Trigger): Seq[Exp]
  protected def Trigger(exps: Seq[Exp]): Trigger

  /* True iff the given node is not allowed in triggers */
  protected def isForbiddenInTrigger(e: Exp): Boolean

  /*
   * Abstract members - dependencies
   */

  protected val solver: GenericArithmeticSolver[Type, Exp, Var, Plus, Minus]

  protected def fresh(name: String, typ: Type): Var

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  protected def log(message: String): Unit

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  protected def log(key: String, item: Any): Unit

  @scala.annotation.elidable(level = scala.annotation.elidable.ASSERTION)
  protected def log(key: String, items: Iterable[Any]): Unit

  /*
   * Actual implementation
   */

  def extractInvalidTermsInTriggerSets(triggers: Seq[TriggerSet]): Seq[Seq[ForbiddenInTrigger]] =
    /* Note that we use shallow collect here. As a consequence, for a trigger
     * 'f(x + (N - 1))', the returned invalid terms will be 'x + (N - 1)' only,
     * and not both 'x + (N - 1)' and 'N - 1'.
     *
     * This difference might matter if multiple quantified variables occur in
     * an invalid term, e.g. as in 'f(x + (y - 1))'.
     */
    triggers flatMap (_.exps map (Exp_shallowCollect(_) {
      case s: ForbiddenInTrigger if isForbiddenInTrigger(s) => s }))

  protected def partitionInvalidTerms(invalidTerms: ListSet[ForbiddenInTrigger],
                                      qvars: Seq[Var])
                                     : (Seq[ForbiddenInTrigger],
                                        Seq[ForbiddenInTrigger],
                                        Map[Var, ListSet[ForbiddenInTrigger]]) = {

    val empty = (List[ForbiddenInTrigger](),
                 List[ForbiddenInTrigger](),
                 Map[Var, ListSet[ForbiddenInTrigger]]())

    val result @ (invalidTermsWithNoQVar, invalidTermsWithMultipleQVars, qvarsToTerms) =
      invalidTerms.foldLeft(empty){case ((accNo, accMultiple, map), term) =>
        val containedQVars = qvars filter (Exp_contains(term, _))

        if (containedQVars.isEmpty) /* term contains no quantified variable */
          (term +: accNo, accMultiple, map)
        else if (containedQVars.tail.isEmpty) { /* term contains exactly one quantified variable */
          val qvar = containedQVars.head
          val qvarTerms = map.getOrElse(qvar, ListSet[ForbiddenInTrigger]()) + term

          (accNo, accMultiple, map + (qvar -> qvarTerms))
        } else /* term contains more than one quantified variable */
          (accNo, term +: accMultiple, map)
      }

    assert(   invalidTermsWithNoQVar.size
           +  invalidTermsWithMultipleQVars.size
           +  qvarsToTerms.values.flatten.size
           == invalidTerms.size,
           "Sum of terms doesn't match")

    result
  }

  protected def solve(qvarsToInvalidTerms: Map[Var, ListSet[ForbiddenInTrigger]])
                     : (Map[Var, ListSet[(ForbiddenInTrigger, Var, Exp)]], // [XXX] Node instead of Exp?
                        Map[Var, ListSet[ForbiddenInTrigger]]) = {

    var solved = Map[Var, ListSet[(ForbiddenInTrigger, Var, Exp)]]() // [XXX] Node instead of Exp?
    var unsolved = Map[Var, ListSet[ForbiddenInTrigger]]()

    for ((qvar, terms) <- qvarsToInvalidTerms;
         term <- terms) {

      val freshQVar = fresh(Var_id(qvar), Exp_type(term))

      solver.solve(freshQVar, term, qvar) match {
        case solver.SolvingSuccess(`qvar`, t) =>
          val entries = solved.getOrElse(qvar, ListSet()) + ((term, freshQVar, t)) /* t_i(x_i), u_i, t'_i(u_i) */
          solved += (qvar -> entries)
        case err =>
          assert (!err.isInstanceOf[solver.SolvingSuccess], s"Found unexpected success $err")
          log("err", err)

          val entries = unsolved.getOrElse(qvar, ListSet()) + term
          unsolved += (qvar -> entries)
      }
    }

    assert((solved.keys ++ unsolved.keys).toSet.size == qvarsToInvalidTerms.keys.size,
           "Sum of quantified variables doesn't match")

    assert(solved.values.flatten.size + unsolved.values.flatten.size == qvarsToInvalidTerms.values.flatten.size,
           "Sum of terms doesn't match")

    (solved, unsolved)
  }

  def rewrite(quantification: Quantification, triggerSets: Seq[TriggerSet]): Option[Quantification] = {
    /* Step 1: Extract the set of invalid terms that occur in triggers, and
     * perform a few initial checks to see if we can potentially rewrite them.
     */

    /* Replacing the invalid trigger terms later on can potentially be improved
     * w.r.t. performance if we remembered from which trigger set which invalid
     * terms have been extracted. The performance gain is probably negligible,
     * though.
     */
    val invalidTerms: ListSet[ForbiddenInTrigger] =
      ListSet(extractInvalidTermsInTriggerSets(triggerSets).flatten: _*)

    if (invalidTerms.isEmpty)
    /* Nothing needs to be rewritten */
      return Some(quantification)

    log(s"\n--- --- [AxiomRewriter] --- ---\n$quantification\n")
    log("invalidTerms", invalidTerms)

    val (invalidTermsWithNoQVar, invalidTermsWithMultipleQVars, qvarsToInvalidTerms) =
      partitionInvalidTerms(invalidTerms, Quantification_vars(quantification))

    if (invalidTermsWithNoQVar.nonEmpty) log("invalidTermsWithNoQVar", invalidTermsWithNoQVar)
    if (invalidTermsWithMultipleQVars.nonEmpty) log("invalidTermsWithMultipleQVars", invalidTermsWithMultipleQVars)

    if (invalidTermsWithNoQVar.nonEmpty || invalidTermsWithMultipleQVars.nonEmpty)
    /* Cannot currently handle these situations */
      return None

    log("qvarsToInvalidTerms", qvarsToInvalidTerms)


    /* Step 2: Introduce a fresh variable u_i per term t_i(x_i), where x_i
     * is a quantified variable, and try to solve u_i = t_i(x_i) for x_i,
     * yielding x_i = x_i = t'_i(u_i), if successful.
     */

    val (solved, unsolved) = solve(qvarsToInvalidTerms)

    if (unsolved.nonEmpty) {
      /* We could not rewrite all terms. Let's be conservative and not change anything. */
      log("unsolved", unsolved)

      return None
    }

    assert(solved.nonEmpty)
    /* At this point, solved should not be empty. Either there was nothing to
     * rewrite, in which case we should have exited early on, or there were
     * terms to rewrite but we couldn't rewrite (some of) them, in which case
     * we should have exited already.
     */

    log(s"Rewrote all invalid terms")
    log("solved", solved)


    /* Step 3: Rewrite each occurrence of t_ij(x_i) with u_ij, in the triggers
     * and in the quantifier body. Note that the rewritten triggers/body may
     * still contain occurrences of x_i.
     */

    var rewrittenTriggerSets = triggerSets
    var rewrittenBody = Quantification_body(quantification)

    for ((qvar, entries) <- solved;
         (invalidTerm, substVar, solution) <- entries) {

      /* Replace each occurrence of invalidTerm with substVar */
      rewrittenTriggerSets =
        rewrittenTriggerSets.map(trigger =>
          TriggerSet(trigger.exps.map(Exp_replace(_, invalidTerm, substVar))))

      rewrittenBody = Exp_replace(rewrittenBody, invalidTerm, substVar)
    }

    assert(rewrittenTriggerSets.size == triggerSets.size)
    assert(rewrittenTriggerSets.flatMap(_.exps).size == triggerSets.flatMap(_.exps).size)

    /* Step 4: Determine quantified variables that are no longer used in the
     * triggers, and replace potential occurrences of them in the quantifier
     * body with t'_i1(u_i1).
     */

    val unusedQVars =
      solved.flatMap{case (qvar, entries) =>
        if (rewrittenTriggerSets.exists(_.exps.exists(Exp_contains(_, `qvar`)))) None
        else Some(qvar)}

    for ((qvar, entries) <- solved
         if unusedQVars.exists(_ == qvar)) {

      rewrittenBody = Exp_replace(rewrittenBody, qvar, entries.head._3)
    }

    /* Step 5 - Constrain newly introduced quantified variables:
     *   - Append conjuncts encoding
     *       t'_i1(x_i) == t'_i2(x_i) == .. == t'_in(x_i)
     *     to the body
     *   - Append conjunct
     *       x_i == t'_i1(x_i)
     *     to the body iff  x_i still occurs in the rewritten triggers
     */

    val equalityComponents =
      solved.flatMap{case (qvar, entries) => (
           (if (unusedQVars.exists(_ == qvar)) Nil
            else qvar :: Nil)
        ++ entries.map(_._3))}

    assert(equalityComponents.nonEmpty) /* Similar to solved not being empty, see comment above */

    val equalities =
      if (equalityComponents.tail.isEmpty) Nil
      else equalityComponents.sliding(2).map{case Seq(t1: Exp, t2: Exp) => Eq(t1, t2)}

    /* Attention: Changing the structure of the body of a quantifier might interfere with
     * recognising valid quantified permission assertions.
     */
    rewrittenBody = Implies(And(equalities.toSeq), rewrittenBody)

    /* Step 5 - Create rewritten quantification */

    val newQVars = (
         Quantification_vars(quantification).filterNot(qvar => unusedQVars.exists(_ == qvar))
      ++ solved.values.flatMap(_.map(_._2)))

    val rewrittenTriggers = rewrittenTriggerSets.map(set => Trigger(set.exps))

    val rewrittenQuantification =
      Quantification_copy(quantification, newQVars, rewrittenBody, rewrittenTriggers)

    log("\nRewritten quantification:")
    log(s"  $rewrittenQuantification")

    Some(rewrittenQuantification)
  }
}
