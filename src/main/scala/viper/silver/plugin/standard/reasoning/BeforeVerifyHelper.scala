// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

package viper.silver.plugin.standard.reasoning

import org.jgrapht.graph.DefaultEdge
import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Apply, Exhale, Exp, FieldAssign, Fold, Inhale, LocalVar, LocalVarDecl, Method, MethodCall, Package, Position, Program, Seqn, Stmt, Unfold}
import viper.silver.plugin.standard.reasoning.analysis.VarAnalysisGraph
import viper.silver.plugin.standard.termination.{DecreasesSpecification, DecreasesStar, DecreasesTuple, DecreasesWildcard}
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable
import scala.jdk.CollectionConverters.CollectionHasAsScala

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
      var containsDecreases = false
      if (containsLemma) {
        /** check preconditions for decreases clause */
        method.pres.foreach {
          case DecreasesTuple(_, _) =>
            containsDecreases = true
          case DecreasesWildcard(_) =>
            containsDecreases = true
          case DecreasesStar() =>
            reportError(ConsistencyError("decreases statement might not prove termination", method.pos))
          case _ =>
            ()
        }
        /** check postconditions for decreases clause */
        method.posts.foreach {
          case DecreasesTuple(_, _) =>
            containsDecreases = true
          case DecreasesWildcard(_) =>
            containsDecreases = true
          case DecreasesStar() =>
            reportError(ConsistencyError("decreases statement might not prove termination", method.pos))
            containsDecreases = true
          case _ => ()
        }

        /** check info for decreases specification */
        method.meta._2 match {
          case spec: DecreasesSpecification =>
            if (spec.star.isDefined) {
              reportError(ConsistencyError("decreases statement might not prove termination", method.pos))
              containsDecreases = true
            } else {
              containsDecreases = true
            }
          case _ =>
        }
      }

      /** report error if there is no decreases clause or specification */
      if (containsLemma && !containsDecreases) {
        reportError(ConsistencyError(s"method ${method.name} marked lemma might not contain decreases clause", method.pos))
      }

      /** check method body for impure statements */
      if (containsLemma) {
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

  /** check that influenced by expressions are exact or overapproximate the body of the method. */
  def checkInfluencedBy(input: Program, reportError: AbstractError => Unit): Unit = {
    val body_graph_analysis: VarAnalysisGraph = VarAnalysisGraph(input, reportError)
    input.methods.foreach(method => {
      var return_vars = method.formalReturns.toSet ++ Seq(body_graph_analysis.heap_vertex)
      val arg_vars = method.formalArgs.toSet ++ Seq(body_graph_analysis.heap_vertex)

      /** helper variable for error message, maps local variable to its position */
      var influenced_by_pos: Map[LocalVarDecl, Position] = Map()


      val init_args_decl = method.formalArgs.map(a => body_graph_analysis.createInitialVertex(a))
      val init_rets_decl = method.formalReturns.map(r => body_graph_analysis.createInitialVertex(r))
      val method_vars: Map[LocalVarDecl, LocalVarDecl] = ((method.formalArgs zip init_args_decl) ++ (method.formalReturns zip init_rets_decl) ++ Seq((body_graph_analysis.heap_vertex, body_graph_analysis.createInitialVertex(body_graph_analysis.heap_vertex)))).toMap
      val empty_body_graph = body_graph_analysis.createEmptyGraph(method_vars)
      val heap_vert = LocalVarDecl(body_graph_analysis.heap_vertex.name, body_graph_analysis.heap_vertex.typ)()

      val influenced_graph = body_graph_analysis.copyGraph(empty_body_graph)
      var influenced_exists: Boolean = false
      /** iterate through method postconditions to find flow annotations */
      method.posts.foreach {
        case v@FlowAnnotation(target, args) =>
          influenced_exists = true

          /** create target variable of flowannotation based on whether it is the heap or another return variable */
          val target_var: LocalVar = target match {
            case value: Var => value.decl
            case _ => body_graph_analysis.heap_vertex.localVar
          }
          val target_decl: LocalVarDecl = LocalVarDecl(target_var.name, target_var.typ)(v.pos)

          /** check whether the target variable is in fact a return variable */
          if (!return_vars.contains(target_decl)) {
            reportError(ConsistencyError(s"Only return variables can be influenced and only one influenced by expression per return variable can exist. ${target_decl.name} may not be a return variable or might be used several times.", v.pos))
          }
          /** keep track of which return variables have an influenced by annotation */
          return_vars -= target_decl
          influenced_by_pos += (target_decl -> v.pos)


          args.foreach(arg => {

            /** decide for each variable in the set of variables of the flow annotation whether they represent a normal variable or the heap */
            val arg_var: LocalVar = arg match {
              case value: Var => value.decl
              case _ => body_graph_analysis.heap_vertex.localVar
            }
            val arg_decl: LocalVarDecl = LocalVarDecl(arg_var.name, arg_var.typ)(arg_var.pos)

            /** check that each variable in the set is a method argument */
            if (!arg_vars.contains(arg_decl)) {
              reportError(ConsistencyError(s"Only argument variables can be influencing the return variable. ${arg_decl.name} may not be an argument variable.", v.pos))
            }

            /** add corresponding edge from method argument to the target variable */
            influenced_graph.addEdge(method_vars(arg_decl), target_decl, new DefaultEdge)
          })
        case _ => ()

      }
      /** for all remaining variables that didn't have an influenced by annotation create an edge from every method argument to the return variable
        * to overapproximate the information flow
        */
      return_vars.foreach(rv => {
        (method.formalArgs ++ Seq(body_graph_analysis.heap_vertex)).foreach(a => {
          if (!influenced_graph.containsVertex(method_vars(a))) {
            influenced_graph.addVertex(method_vars(a))
          }
          if (!influenced_graph.containsVertex(rv)) {
            influenced_graph.addVertex(rv)
          }
          influenced_graph.addEdge(method_vars(a), rv, new DefaultEdge)
        })
      })

      /** for evaluation purposes if graph of method body should be created even though there is no influenced by annotation */
      //val body_graph = body_graph_analysis.compute_graph(method.body.getOrElse(Seqn(Seq(), Seq())()), method_vars)

      /** if influenced by annotation exists create graph of the method body and check whether the influenced by expression is correct */
      if (influenced_exists) {
        val body_graph = body_graph_analysis.compute_graph(method.body.getOrElse(Seqn(Seq(), Seq())()), method_vars)

        /** ignore the edges from the .init_ret to the ret vertex since before the method there is no init value of a return variable. */
        method.formalReturns.foreach(r => {
          body_graph.removeAllEdges(method_vars(r), r)
        })

        /** the set of all incoming edges to the return variables of the method body graph should be a subset of the set of the incoming edges of the influenced by graph */
        (method.formalReturns ++ Seq(heap_vert)).foreach(r => {
          body_graph.incomingEdgesOf(r).forEach(e => {
            if (!influenced_graph.containsEdge(body_graph.getEdgeSource(e), body_graph.getEdgeTarget(e))) {
              val ret_sources: String = body_graph.incomingEdgesOf(r).asScala.map(e => body_graph.getEdgeSource(e).name).toList.sortWith(_ < _).mkString(", ").replace(".init_", "").replace(".", "")
              reportError(ConsistencyError("influenced by expression may be incorrect. Possible influenced by expression: \n" + "influenced " + r.name.replace(".", "") + " by {" + ret_sources + "}", influenced_by_pos(r)))
            }
          })
        })
      }
    })
  }
}
