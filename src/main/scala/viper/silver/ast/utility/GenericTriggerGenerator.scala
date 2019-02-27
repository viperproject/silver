// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import reflect.ClassTag

object GenericTriggerGenerator {
  case class TriggerSet[E](exps: Seq[E])
}

/** Attention: The trigger generator is *not* thread-safe, among other things because its
  * filters for accepting/rejecting possible triggers can be changed
  * (see, e.g. [[GenericTriggerGenerator.setCustomIsForbiddenInTrigger]]).
  */
abstract class GenericTriggerGenerator[Node <: AnyRef,
                                       Type <: AnyRef,
                                       Exp  <: Node : ClassTag,
                                       Var <: Node : ClassTag,
                                       Quantification <: Exp : ClassTag] extends Mutable {
  /* 2014-09-22 Malte: I tried to use abstract type members instead of type
   * parameters, but that resulted in the warning "The outer reference in this
   * type test cannot be checked at run time.".
   */

  type TriggerSet = GenericTriggerGenerator.TriggerSet[Exp]
  val TriggerSet = GenericTriggerGenerator.TriggerSet

  private type PossibleTrigger = Exp
  private type ForbiddenInTrigger = Exp

  /* Node */
  protected def hasSubnode(root: Node, child: Node): Boolean
  protected def visit[A](root: Node)(f: PartialFunction[Node, A])
  protected def deepCollect[A](root: Node)(f: PartialFunction[Node, A]): Seq[A]
  protected def reduceTree[A](root: Node)(f: (Node, Seq[A]) => A): A
  protected def transform[N <: Node](root: N)(f: PartialFunction[Node, Node]): N

  /* Exp */
  protected def Exp_typ(exp: Exp): Type

  /* Var */
  protected def Var(id: String, typ:  Type): Var

  /* QuantiQuantifiedExp */
  protected def Quantification_vars(q: Quantification): Seq[Var]

  /* True iff the given node is a possible trigger */
  protected def isPossibleTrigger(e: Exp): Boolean

  protected def withArgs(e: Exp, args: Seq[Exp]): Exp
  protected def getArgs(e: Exp): Seq[Exp]

  /* True iff the given node is not allowed in triggers */
  def isForbiddenInTrigger(e: Exp): Boolean

  protected var customIsPossibleTrigger: PartialFunction[Exp, Boolean] = PartialFunction.empty
  def setCustomIsPossibleTrigger(f: PartialFunction[Exp, Boolean]) { customIsPossibleTrigger = f }

  protected var customIsForbiddenInTrigger: PartialFunction[Exp, Boolean] = PartialFunction.empty
  def setCustomIsForbiddenInTrigger(f: PartialFunction[Exp, Boolean]) { customIsForbiddenInTrigger = f }

  private var nextUniqueId = 0

  def generateTriggerSetGroup(vs: Seq[Var], toSearch: Exp): Option[(Seq[TriggerSet], Seq[Var])] =
    generateTriggerSetGroups(vs: Seq[Var], toSearch: Exp).headOption

  def generateFirstTriggerSetGroup(vs: Seq[Var], toSearch: Seq[Exp]): Option[(Seq[TriggerSet], Seq[Var])] =
    /* TODO: It would be better to increase the set of terms from which triggers
     * can be computed. That is, if toSearch = [e1, e2, ..., en], then
     * generateTriggers(e1) should be tried first, then generateTriggers(e1, e2),
     * etc. This is, because it could be that only the combination of multiple
     * ei's provides enough terms to cover all quantified variables.
     */
    toSearch.toStream.flatMap(generateTriggerSetGroup(vs, _)).headOption

  def generateStrictestTriggerSet(vs: Seq[Var], toSearch: Exp): Option[(TriggerSet, Seq[Var])] =
    generateTriggerSetGroups(vs, toSearch).headOption.map { case (triggerSets, vars) =>
      val triggerExps = triggerSets.foldLeft(Set[Exp]())((acc, trigger) => acc ++ trigger.exps)

      (TriggerSet(triggerExps.toSeq), vars)
    }

  /* Generates groups of trigger sets to cover the variables `vs`, by searching
   * the expression `toSearch`.
   *
   * Returns a list of pairs of lists of trigger sets couple with the extra
   * variables they require to be quantified over (each list of triggers must
   * contain trigger sets which employ exactly the same extra variables).
   */
  def generateTriggerSetGroups(vs: Seq[Var], toSearch: Exp): Seq[(Seq[TriggerSet], Seq[Var])] = {
    /* Find suitable function applications */
    val functionApps: (Seq[(PossibleTrigger, Seq[Var], Seq[Var])]) =
      getFunctionAppsContaining(vs, toSearch)

    if (functionApps.isEmpty)
      Seq()
    else {
      val candidates: Seq[(TriggerSet, Seq[Var])] = buildTriggersCovering(vs, functionApps, Nil, Seq())

      /* Filter out any trigger sets with redundant terms, e.g., for {g(x),f(g(x))}
       * the entire set is dropped, since the version without redundancy will
       * also be found, i.e., {f(g(x))},
       */
      val filteredCandidates: Seq[(TriggerSet, Seq[Var])] =
        candidates.filterNot { case (trigger, _) =>
          trigger.exps.exists(exp1 => trigger.exps.exists(exp2 => hasSubnode(exp1, exp2)))}

      /* Remove any trigger sets which are "subsumed" by another trigger set (in
       * the sense that they define a strictly weaker criterion), as well as any duplicates.
       * The criterion used here is that a set is weaker than another iff every
       * term in the first set is a strict subterm of some term in the second
       * set.
       * Note that it may be that this criterion could be generalised (using
       * some unification to spot e.g. that f(g(x),g(y)) is stricter than
       * f(x,y), but this is not done here.
       */
      var triggerSetsToUse: Seq[(TriggerSet, Seq[Var])] =
        filteredCandidates.distinct.filterNot { case pair1 @ (trigger1, vs1) =>
          filteredCandidates.exists { case pair2 @ (trigger2, vs2) => (
               pair1 != pair2 && vs1.toSet == vs2.toSet // only "subsumed" if we don't need to bind more variables, otherwise the simpler option may really be simpler
            && trigger1.exps.forall(exp1 => trigger2.exps.exists(exp2 => hasSubnode(exp2, exp1))))
          }
        }

      /* Group trigger sets by those which use the same sets of extra boolean variables */
      var groupedTriggerSets: Seq[(Seq[TriggerSet], Seq[Var])] = Seq()

      while (triggerSetsToUse.nonEmpty) {
        triggerSetsToUse.partition(ts => triggerSetsToUse.head._2.equals(ts._2)) match {
          case (sameVars, rest) =>
            triggerSetsToUse = rest
            groupedTriggerSets +:=(sameVars map (_._1), sameVars.head._2.toList)
        }
      }

      groupedTriggerSets.sortBy(_._2.size)
    }
  }

  /* This is used for searching for triggers for quantifiers around the
   * expression "toSearch". The list "vs" gives the variables which need
   * triggering.
   *
   * Returns a list of function applications (the framing function) paired
   * with two sets of variables. The first set of variables shows which of the
   * "vs" occur (useful for deciding how to select applications for trigger
   * sets later). The second set of variables indicated the extra boolean
   * variables which were introduced to "hide" problematic logical/comparison
   * operators which may not occur in triggers.
   *
   * E.g., if vs = [x] and toSearch = f(x, y ==> z) than a singleton list will
   * be returned, containing (f(x,b),{x},{b}).
   */
  def getFunctionAppsContaining(vs: Seq[Var], toSearch: Exp)
                               : (Seq[(PossibleTrigger, Seq[Var], Seq[Var])]) = {


    /* Get all variables bound in nested quantifiers, to avoid considering
     * function applications mentioning these */
    val nestedBoundVars: Seq[Var] =
      deepCollect(toSearch){ case qe: Quantification => Quantification_vars(qe)}.flatten

    /* Get all function applications */
    reduceTree(toSearch)((node: Node, results: Seq[Seq[(PossibleTrigger, Seq[Var], Seq[Var])]]) => node match {
      case possibleTrigger: PossibleTrigger if isPossibleTrigger(possibleTrigger) =>
        var extraVars: Seq[Var] = Seq() /* Collect extra variables generated for this term */
        var containsNestedBoundVars = false /* Flag to rule out this term */
        var containedVars: Seq[Var] = Seq()

        /* Eliminate all boolean expressions forbidden from triggers, and
         * replace with "extraVars"
         */
        val processedArgs = getArgs(possibleTrigger) map (pt => transform(pt) {
          case e: Exp if isForbiddenInTrigger(e) =>
            val newV = Var("fresh__" + nextUniqueId, Exp_typ(e))
            nextUniqueId += 1
            extraVars +:= newV

            newV
        })

        /* Collect all the sought (vs) variables in the function application */
        processedArgs foreach (arg => visit(arg) {
          case v: Var =>
            if (nestedBoundVars.contains(v)) containsNestedBoundVars = true
            if (vs.contains(v)) containedVars +:= v
        })

        if (!containsNestedBoundVars && containedVars.nonEmpty)
          results.flatten ++ Seq((withArgs(possibleTrigger, processedArgs), containedVars, extraVars))
        else
          results.flatten

      case _ => results.flatten
    })
  }

  /* Precondition: if vars is non-empty then every (f,vs) pair in functs
   * satisfies the property that vars and vs are not disjoint.
   *
   * Finds trigger sets by selecting entries from "functs" until all of "vars"
   * occur, and accumulating the extra variables needed for each function term.
   * Returns a list of the trigger sets found, paired with the extra boolean
   * variables they use
   */
  def buildTriggersCovering(vars: Seq[Var],
                            functs: Seq[(PossibleTrigger, Seq[Var], Seq[Var])],
                            currentTrigger: Seq[Exp],
                            extraVars: Seq[Var])
                           : Seq[(TriggerSet, Seq[Var])] = {

    if (vars.isEmpty)
      /* We have found a suitable trigger set */
      Seq((TriggerSet(currentTrigger), extraVars))
    else functs match {
      case Nil => Nil /* This branch didn't result in a solution */
      case ((f, vs, extra) +: rest) =>
        val needed: Seq[Var] = vars.diff(vs) /* Variables still not triggered */

        /* Try adding the next element of functs */
        var result =
          buildTriggersCovering(needed,
                                rest.filter(func => func._2.intersect(needed).nonEmpty),
                                currentTrigger :+ f,
                                (extraVars ++ extra).distinct)

        result ++= buildTriggersCovering(vars, rest, currentTrigger, extraVars)

        result
    }
  }
}
