// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning


import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Apply, Declaration, Exhale, Exp, FieldAssign, Fold, Inhale, LocalVarDecl, Method, MethodCall, Package, Program, Seqn, Stmt, Unfold}
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.plugin.standard.reasoning.analysis.AnalysisUtils

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
    * get all variables that are assigned to inside the block and take intersection with universal introduction
    * variables. If they are contained throw error since these variables should be immutable
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

  private def specifiesLemma(m: Method): Boolean = (m.pres ++ m.posts).exists {
    case _: Lemma => true
    case _ => false
  }
  
  /** check if isLemma precondition is correct */
  def checkLemma(input: Program, reportError: AbstractError => Unit): Unit = {
    input.methods.foreach(method => {
      val containsLemma = specifiesLemma(method)
      val (containsDecreases, containsDecreasesStar) = AnalysisUtils.containsDecreasesAnnotations(method)

      if (containsLemma) {
        /** report error if there is no decreases clause or specification */
        if(!containsDecreases) {
          reportError(ConsistencyError(s"method ${method.name} marked lemma might not contain decreases clause", method.pos))
        }

        /** report error if the decreases statement might not prove termination */
        if (containsDecreasesStar) {
          reportError(ConsistencyError("decreases statement might not prove termination", method.pos))
        }

        /** check method body for impure statements */
        checkBodyPure(method.body.getOrElse(Seqn(Seq(), Seq())()), method, input, reportError)
      }
    })
  }

  /** checks whether the body is pure, reports error if impure operation found */
  def checkBodyPure(stmt: Stmt, method: Method, prog: Program, reportError: AbstractError => Unit): Boolean = {
    var pure: Boolean = true
    stmt match {
      case Seqn(ss, _) =>
        ss.foreach(s => {
          pure = pure && checkBodyPure(s, method, prog, reportError)
        })
        pure

        /** case for statements considered impure */
      case ie@(Inhale(_) | Exhale(_) | FieldAssign(_, _) | Fold(_) | Unfold(_) | Apply(_) | Package(_, _)) =>
        reportError(ConsistencyError(s"method ${method.name} marked lemma might contain impure statement ${ie}", ie.pos))
        false
      case m@MethodCall(methodName, _, _) =>
        val mc = prog.findMethod(methodName)
        val containsLemma = specifiesLemma(mc)

        /** if called method is not a lemma report error */
        if (!containsLemma) {
          reportError(ConsistencyError(s"method ${method.name} marked lemma might contain call to method ${m}", m.pos))
          false
        } else {
          pure
        }
      case _ =>
        pure
    }
  }

  /** checks that influences by annotations are used correctly. */
  def checkInfluencedBy(input: Program, reportError: AbstractError => Unit): Unit = {
    input.methods.foreach(method => {
      val argVars = method.formalArgs.toSet + AnalysisUtils.heapVertex
      val retVars = method.formalReturns.toSet.asInstanceOf[Set[Declaration]] + AnalysisUtils.heapVertex + AnalysisUtils.AssumeNode(method.pos)

      val seenVars: mutable.Set[Declaration] = mutable.Set()
      /** iterate through method postconditions to find flow annotations */
      method.posts.foreach {
        case v@FlowAnnotation(target, args) =>
          val targetVarDecl = AnalysisUtils.getDeclarationFromFlowVar(target, method)

          if (!retVars.contains(targetVarDecl)) {
            reportError(ConsistencyError(s"Only return variables can be influenced. ${targetVarDecl.name} is not be a return variable.", v.pos))
          }
          if (seenVars.contains(targetVarDecl)) {
            reportError(ConsistencyError(s"Only one influenced by expression per return variable can exist. ${targetVarDecl.name} is used several times.", v.pos))
          }
          seenVars.add(targetVarDecl)

          args.foreach(arg => {
            val argVarDecl = AnalysisUtils.getLocalVarDeclFromFlowVar(arg)
            if (!argVars.contains(argVarDecl)) {
              reportError(ConsistencyError(s"Only method arguments can influence a return variable. ${argVarDecl.name} is not be a method argument.", v.pos))
            }
          })
        case _ => ()
      }
    })
  }
}