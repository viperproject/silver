// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning


import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Apply, Exhale, Exp, FieldAssign, Fold, Inhale, LocalVarDecl, Method, MethodCall, Package, Program, Seqn, Stmt, Unfold}
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils.{AssumeInfluenceSink, InfluenceSink}

import scala.collection.mutable

trait BeforeVerifyHelper {
  /** methods to rename variables for the encoding of the new syntax */
  def uniqueName(name: String, usedNames: mutable.Set[String]): String = {
    var i = 1
    var newName = name
    while (usedNames.contains(newName)) {
      newName = name + i
      i += 1
    }
    usedNames.add(newName)
    newName
  }

  def substituteWithFreshVars[E <: Exp](vars: Seq[LocalVarDecl], exp: E, usedNames: mutable.Set[String]): (Seq[(LocalVarDecl, LocalVarDecl)], E) = {
    val declMapping = vars.map(oldDecl =>
      oldDecl -> LocalVarDecl(uniqueName(oldDecl.name, usedNames), oldDecl.typ)(oldDecl.pos, oldDecl.info, oldDecl.errT))
    val transformedExp = applySubstitution(declMapping, exp)
    (declMapping, transformedExp)
  }

  def applySubstitution[E <: Exp](mapping: Seq[(LocalVarDecl, LocalVarDecl)], exp: E): E = {
    Expressions.instantiateVariables(exp, mapping.map(_._1.localVar), mapping.map(_._2.localVar))
  }

  def applySubstitutionWithExp[E <: Exp](mapping: Seq[(LocalVarDecl, Exp)], exp: E): E = {
    Expressions.instantiateVariables(exp, mapping.map(_._1.localVar), mapping.map(_._2))
  }
  
  /**
    * check that all variables (`modified_vars`) that are assigned to inside a universal introduction `u`'s block are
    * distinct from the universal introduction `u`'s quantified variables `quantified_vars`. Otherwise, an error is
    * reported via `reportError` since these quantified variables should be immutable.
    *
    * @param modified_vars: set of variables that were modified in a given statement
    * @param quantified_vars: set of quantified variables in the universal introduction statement.
    * @param reportError: Method to report the error when a qunatified variable was modified
    * @param u: universal introduction statement, used for details in error message
    */
  def checkReassigned(modified_vars: Set[LocalVarDecl], quantified_vars: Seq[LocalVarDecl], reportError: AbstractError => Unit, u: UniversalIntro): Unit = {
      val reassigned_vars: Set[LocalVarDecl] = modified_vars.intersect(quantified_vars.toSet)
      if (reassigned_vars.nonEmpty) {
        val reassigned_names: String = reassigned_vars.mkString(", ")
        val reassigned_pos: String = reassigned_vars.map(_.pos).mkString(", ")
        reportError(ConsistencyError("Universal Introduction variable(s) (" + reassigned_names + ") might have been reassigned at position(s) (" + reassigned_pos + ")", u.pos))
      }
  }

  /** returns true if method `m` is annotated to be a lemma */
 def specifiesLemma(m: Method): Boolean = (m.pres ++ m.posts).exists {
    case _: Lemma => true
    case _ => false
  }
  
  /** Checks that all lemmas in `input` satisfy the syntactical restrictions and, otherwise, reports errors by invoking `reportError`.  */
  def checkLemmas(input: Program, reportError: AbstractError => Unit): Unit = {
    input.methods.foreach(method => {
      val containsLemma = specifiesLemma(method)
      val terminationSpecState = AnalysisUtils.specifiesTermination(method)

      if (containsLemma) {
        // lemmas must terminate. We report slightly different errors depending on the cause:
        if (!terminationSpecState.guaranteesTermination) {
          if (terminationSpecState.noTerminationSpec) {
            reportError(ConsistencyError(s"Lemmas must terminate but method ${method.name} marked lemma does not specify any termination measures", method.pos))
          } else {
            reportError(ConsistencyError(s"Lemmas must terminate but the specification of method ${method.name} might not guarantee termination", method.pos))
          }
        }

        /** check method body for impure statements */
        checkStmtPure(method.body.getOrElse(Seqn(Seq.empty, Seq.empty)()), method, input, reportError)
      }
    })
  }

  /** checks whether a statement `stmt` is pure, reports error if impure operation found */
  def checkStmtPure(stmt: Stmt, method: Method, prog: Program, reportError: AbstractError => Unit): Boolean = {
    stmt match {
      case Seqn(ss, _) =>
        ss.forall(s => checkStmtPure(s, method, prog, reportError))

        /** case for statements considered impure */
      case ie@(Inhale(_) | Exhale(_) | FieldAssign(_, _) | Fold(_) | Unfold(_) | Apply(_) | Package(_, _)) =>
        reportError(ConsistencyError(s"method ${method.name} marked lemma might contain impure statement $ie", ie.pos))
        false
      case m@MethodCall(methodName, _, _) =>
        val mc = prog.findMethod(methodName)
        val isLemmaCall = specifiesLemma(mc)

        /** if called method is not a lemma report error */
        if (!isLemmaCall) {
          reportError(ConsistencyError(s"method ${method.name} marked lemma might contain call to method $m", m.pos))
        }
        isLemmaCall
      case _ => true
    }
  }

  /** checks that all influences by annotations in `input` are used correctly. */
  def checkInfluencedBy(input: Program, reportError: AbstractError => Unit): Unit = {
    input.methods.foreach(method => {
      val argSources = method.formalArgs.map(AnalysisUtils.getSourceFromVarDecl).toSet + AnalysisUtils.HeapSource
      val retSinks = method.formalReturns.map(AnalysisUtils.getSinkFromVarDecl).toSet + AnalysisUtils.HeapSink + AnalysisUtils.AssumeMethodInfluenceSink(method)

      val seenSinks: mutable.Set[InfluenceSink] = mutable.Set.empty
      /** iterate through method postconditions to find flow annotations */
      method.posts.foreach {
        case v@InfluencedBy(target, args) =>
          val declaredSink = AnalysisUtils.getSinkFromFlowVar(target, method)

          if (!retSinks.contains(declaredSink)) {
            reportError(ConsistencyError(s"Only return parameters, the heap or assumes can be influenced but not ${declaredSink.name}.", v.pos))
          }
          if (seenSinks.contains(declaredSink)) {
            reportError(ConsistencyError(s"Only one influenced-by specification per return parameter, heap or assume is allowed. ${declaredSink.name} is used several times.", v.pos))
          }
          seenSinks.add(declaredSink)

          args.foreach(arg => {
            val declaredSource = AnalysisUtils.getSourceFromFlowVar(arg)
            if (!argSources.contains(declaredSource)) {
              reportError(ConsistencyError(s"Only method input parameters or the heap can be sources of influenced-by specifications but not ${declaredSource.name}.", v.pos))
            }
          })
        case _ =>
      }

      // checks that "assume influeced by" and "assumesNothing" are mutually exclusive:
      val assumeNothings = method.posts.collect {
        // case InfluencedBy(_: Assumes, _) =>
        case a: AssumesNothing => a
      }
      val hasAssumeInfluenceSink = seenSinks.exists {
        case _: AssumeInfluenceSink => true
        case _ => false
      }
      if (assumeNothings.length > 1) {
        assumeNothings.foreach(a =>
          reportError(ConsistencyError(s"At most one '${PNothingKeyword.keyword}' permitted per method specification.", a.pos)))
      } else if (assumeNothings.nonEmpty && hasAssumeInfluenceSink) {
        assumeNothings.foreach(a =>
          reportError(ConsistencyError(s"'${PNothingKeyword.keyword}' and '${PInfluencedKeyword.keyword} ${PAssumesKeyword.keyword} ${PByKeyword.keyword} ...' are mutually exclusive.", a.pos)))
      }
    })
  }
}
