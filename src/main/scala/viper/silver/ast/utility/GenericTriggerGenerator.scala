/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import reflect.ClassTag

object GenericTriggerGenerator {
  trait PossibleTrigger[M <: AnyRef, S <: PossibleTrigger[M, S]] {
    def getArgs: Seq[M]
    def withArgs(args: Seq[M]): S
    def asManifestation: M
  }

  trait ForbiddenInTrigger[T] {
    def typ: T
  }

  trait WrappingTrigger[M <: AnyRef, GPT <: PossibleTrigger[M, GPT], S <: WrappingTrigger[M, GPT, S]] extends PossibleTrigger[M, GPT] {
    def wrappee: GPT
  }
}

abstract class GenericTriggerGenerator[Node <: AnyRef,
                                       Type <: AnyRef,
                                       Exp  <: Node,
                                       Var <: Node: ClassTag,
                                       QuantifiedExp <: Exp : ClassTag,
                                       PossibleTrigger <: GenericTriggerGenerator.PossibleTrigger[Exp, PossibleTrigger] : ClassTag,
                                       ForbiddenInTrigger <: GenericTriggerGenerator.ForbiddenInTrigger[Type] : ClassTag,
                                       Old <: Exp : ClassTag,
                                       WrappingTrigger <: PossibleTrigger with GenericTriggerGenerator.WrappingTrigger[Exp, PossibleTrigger, WrappingTrigger] : ClassTag,
                                       Trigger <: AnyRef] {

  /* 2014-09-22 Malte: I tried to use abstract type members instead of type
   * parameters, but that resulted in the warning "The outer reference in this
   * type test cannot be checked at run time.".
   */

  /* Node */
  protected def hasSubnode(root: Node, child: Node): Boolean
  protected def visit[A](root: Node)(f: PartialFunction[Node, A])
  protected def deepCollect[A](root: Node)(f: PartialFunction[Node, A]): Seq[A]
  protected def reduceTree[A](root: Node)(f: (Node, Seq[A]) => A): A
  protected def transform[N <: Node](root: N)(f: PartialFunction[Node, Node]): N

  /* QuantifiedExp */
  protected def quantifiedVariables(q: QuantifiedExp): Seq[Var]

  /* Trigger */
  protected def exps(t: Trigger): Seq[Exp]

  protected def Var(id: String, typ:  Type): Var
  protected def Trigger(exps: Seq[Exp]): Trigger

  /* Wrapping triggers */
  protected val wrapperMap: Map[Class[_], PossibleTrigger => WrappingTrigger]

  object WrappingGNode {
    def unapply(n: Node): Option[PossibleTrigger => WrappingTrigger] =
      wrapperMap.find{case (clazz, f) => clazz.isInstance(n)}.map(_._2)
  }

  private var nextUniqueId = 0

  /* Generates trigger sets to cover the variables "vs", by searching the
   * expression "toSearch".
   *
   * Returns a list of pairs of lists of trigger sets couple with the extra
   * variables they require to be quantified over (each list of triggers must
   * contain trigger sets which employ exactly the same extra variables).
   */
  def generateTriggers(vs: Seq[Var], toSearch: Exp): Seq[(Seq[Trigger], Seq[Var])] = {
    /* Find suitable function applications */
    val functionApps: (Seq[(PossibleTrigger, Seq[Var], Seq[Var])]) =
      getFunctionAppsContaining(vs, toSearch)

    if (functionApps.isEmpty)
      Seq()
    else {
      val candidates: Seq[(Trigger, Seq[Var])] = buildTriggersCovering(vs, functionApps, Nil, Seq())

      /* Filter out any trigger sets with redundant terms, e.g., for {g(x),f(g(x))}
       * the entire set is dropped, since the version without redundancy will
       * also be found, i.e., {f(g(x))},
       */
      val filteredCandidates: Seq[(Trigger, Seq[Var])] =
        candidates.filterNot { case (trigger, _) =>
          exps(trigger).exists(exp1 => exps(trigger).exists(exp2 => hasSubnode(exp1, exp2)))}

      /* Remove any trigger sets which are "subsumed" by another trigger set (in
       * the sense that they define a strictly weaker criterion).
       * The criterion used here is that a set is weaker than another iff every
       * term in the first set is a strict subterm of some term in the second
       * set.
       * Note that it may be that this criterion could be generalised (using
       * some unification to spot e.g. that f(g(x),g(y)) is stricter than
       * f(x,y), but this is not done here.
       */
      var triggerSetsToUse: Seq[(Trigger, Seq[Var])] =
        filteredCandidates.filterNot { case pair1 @ (trigger1, _) =>
          filteredCandidates.exists { case pair2 @ (trigger2, _) => (
               pair1 != pair2
            && exps(trigger1).forall(exp1 => exps(trigger2).exists(exp2 => hasSubnode(exp2, exp1))))
          }
        }

      /* Group trigger sets by those which use the same sets of extra boolean variables */
      var groupedTriggerSets: Seq[(Seq[Trigger], Seq[Var])] = Seq()

      while (triggerSetsToUse.nonEmpty) {
        triggerSetsToUse.partition(ts => triggerSetsToUse.head._2.equals(ts._2)) match {
          case (sameVars, rest) =>
            triggerSetsToUse = rest
            groupedTriggerSets +:=(sameVars map (_._1), sameVars.head._2.toList)
        }
      }

      groupedTriggerSets
    }
  }

  /** Returns the first group of trigger sets (together with newly introduced
    * variables) returned by `generateTriggers`, or `(Nil, Nil)` if the latter
    * didn't return any group.
    *
    * @param vs Variables to cover by the trigger sets.
    * @param toSearch Expression to generate triggers for.
    * @return A pair of trigger sets and additional variables.
    */
  def chooseTriggers(vs: Seq[Var], toSearch: Exp): (Seq[Trigger], Seq[Var]) =
    generateTriggers(vs, toSearch).headOption.getOrElse((Nil, Nil))

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
      deepCollect(toSearch){ case qe: QuantifiedExp => quantifiedVariables(qe)}.flatten

    /* Get all function applications */
    reduceTree(toSearch)((node: Node, results: Seq[Seq[(PossibleTrigger, Seq[Var], Seq[Var])]]) => node match {
      case WrappingGNode(f) =>
        results.flatten map {case (pt, vars, extras) => (f(pt)/*(pt.pos,pt.info)*/, vars, extras)}

      case possibleTrigger: PossibleTrigger =>
        var extraVars: Seq[Var] = Seq() /* Collect extra variables generated for this term */
        var containsNestedBoundVars = false /* Flag to rule out this term */

        /* Closure to generate fresh LocalVar to replace problematic expressions
         * which may not occur in triggers
         */
        val freshVar: (Type => Var) = ty => {
          val newV = Var("fresh__" + nextUniqueId, ty)
          nextUniqueId += 1
          extraVars +:= newV
          newV
        }

        /* Replaces problematic logical/comparison expressions with fresh
         * boolean variables
         */
        val boolExprEliminator: PartialFunction[Node, Var] = {
          case e: ForbiddenInTrigger => freshVar(e.typ)
        }

        var containedVars: Seq[Var] = Seq()

        /* Eliminate all boolean expressions forbidden from triggers, and
         * replace with "extraVars"
         */
        val processedArgs = possibleTrigger.getArgs map (pt => transform(pt)(boolExprEliminator))

        /* Collect all the sought (vs) variables in the function application */
        processedArgs map (arg => visit(arg) {
          case v: Var =>
            if (nestedBoundVars.contains(v)) containsNestedBoundVars = true
            if (vs.contains(v)) containedVars +:= v
        })

        if (!containsNestedBoundVars && containedVars.nonEmpty)
          results.flatten ++ Seq((possibleTrigger.withArgs(processedArgs), containedVars, extraVars))
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
                           : Seq[(Trigger, Seq[Var])] = {

    if (vars.isEmpty)
      /* We have found a suitable trigger set */
      Seq((Trigger(currentTrigger), extraVars))
    else functs match {
      case Nil => Nil /* This branch didn't result in a solution */
      case ((f, vs, extra) +: rest) =>
        val needed: Seq[Var] = vars.diff(vs) /* Variables still not triggered */

        /* Try adding the next element of functs */
        var result =
          buildTriggersCovering(needed,
                                rest.filter(func => func._2.intersect(needed).nonEmpty),
                                currentTrigger :+ f.asManifestation,
                                (extraVars ++ extra).distinct)

        result ++= buildTriggersCovering(vars, rest, currentTrigger, extraVars)

        result
    }
  }
}
