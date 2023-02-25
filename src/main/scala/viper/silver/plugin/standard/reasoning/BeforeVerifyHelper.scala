package viper.silver.plugin.standard.reasoning

import org.jgrapht.graph.DefaultEdge
import viper.silver.ast.utility.Expressions
import viper.silver.ast.{Apply, Exhale, Exp, FieldAssign, Fold, Inhale, LocalVar, LocalVarDecl, Method, MethodCall, Package, Position, Program, Seqn, Stmt, Unfold}
import viper.silver.plugin.standard.reasoning.analysis.VarAnalysisGraph
import viper.silver.plugin.standard.termination.{DecreasesSpecification, DecreasesTuple, DecreasesWildcard}
import viper.silver.verifier.{AbstractError, ConsistencyError}

import scala.collection.mutable
import scala.jdk.CollectionConverters.CollectionHasAsScala

trait BeforeVerifyHelper {



  /** methods to rename variables */
  def uniqueName(name: String, usedNames: mutable.Set[String]): String = {
    println("usedNames: " + usedNames)
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

  /**
    * get all variables that are assigned to inside the block and take intersection with universal introduction
    * variables. If they are contained throw error since these variables should be immutable
    */
  def checkReassigned(written_vars: Option[Set[LocalVarDecl]], v: Seq[LocalVarDecl], reportError: AbstractError => Unit, u: UniversalIntro): Unit = {
    if (written_vars.isDefined) {
      val reassigned_vars: Set[LocalVarDecl] = written_vars.get.intersect(v.toSet)
      if (reassigned_vars.nonEmpty) {
        val reassigned_names: String = reassigned_vars.mkString(", ")
        val reassigned_pos: String = reassigned_vars.map(_.pos).mkString(", ")
        reportError(ConsistencyError("Universal Introduction variable(s) (" + reassigned_names + ") might have been reassigned at position(s) (" + reassigned_pos + ")", u.pos))
      }
    }
  }


  /** check if isLemma precondition is correct */
  def checkLemma(input: Program, reportError: AbstractError => Unit) = {
    input.methods.foreach(method => {
      var containsLemma: Boolean = method.pres.exists(p => p.isInstanceOf[Lemma])
      containsLemma = (containsLemma || method.posts.exists(p => p.isInstanceOf[Lemma]))
      var containsDecreases = false
      if (containsLemma) {
        /** check preconditions for decreases clause */
        method.pres.foreach {
          case DecreasesTuple(_, _) =>
            containsDecreases = true
          case DecreasesWildcard(_) =>
            containsDecreases = true
          case s@_ =>
            ()
        }
        /** check postconditions for decreases clause */
        method.posts.foreach {
          case DecreasesTuple(_, _) =>
            containsDecreases = true
          case DecreasesWildcard(_) =>
            containsDecreases = true
          case s@_ =>
            ()
        }

        /** check info for decreases specification */
        method.meta._2 match {
          case spec: DecreasesSpecification =>
            if (spec.star.isDefined) {
              reportError(ConsistencyError("decreases statement might not prove termination", method.pos))
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

  /** checks whether the body is pure, reports Error if impure operation found */
  def checkBodyPure(stmt: Stmt, method: Method, prog: Program, reportError: AbstractError => Unit): Boolean = {
    var pure: Boolean = true
    stmt match {
      case Seqn(ss, _) =>
        ss.foreach(s => {
          pure = pure && checkBodyPure(s, method, prog, reportError)
        })
        pure
      case ie@(Inhale(_) | Exhale(_) | FieldAssign(_, _) | Fold(_) | Unfold(_) | Apply(_) | Package(_, _)) =>
        reportError(ConsistencyError(s"method ${method.name} marked lemma might contain impure statement ${ie}", ie.pos))
        false
      case m@MethodCall(methodName, _, _) =>
        val mc = prog.findMethod(methodName)
        var containsLemma: Boolean = mc.pres.exists(p => p.isInstanceOf[Lemma])
        containsLemma = containsLemma || mc.posts.exists(p => p.isInstanceOf[Lemma])

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
      val body_graph = body_graph_analysis.compute_graph(empty_body_graph, method.body.getOrElse(Seqn(Seq(), Seq())()), method_vars)
      val heap_vert = LocalVarDecl(body_graph_analysis.heap_vertex.name, body_graph_analysis.heap_vertex.typ)()

      val influenced_graph = body_graph_analysis.copyGraph(empty_body_graph)
      method.posts.foreach {
        case v@FlowAnnotation(target, args) =>

          val target_var: LocalVar = if (target.isInstanceOf[Var]) target.asInstanceOf[Var].var_decl.asInstanceOf[LocalVar] else body_graph_analysis.heap_vertex.localVar
          val target_decl: LocalVarDecl = LocalVarDecl(target_var.name, target_var.typ)(v.pos)

          if (!return_vars.contains(target_decl)) {
            reportError(ConsistencyError(s"Only return variables can be influenced and only one influenced by expression per return variable can exist. ${target_decl.name} may not be a return variable or might be used several times.", v.pos))
          }
          return_vars -= target_decl
          influenced_by_pos += (target_decl -> v.pos)
          args.foreach(arg => {
            val arg_var: LocalVar = if (arg.isInstanceOf[Var]) arg.asInstanceOf[Var].var_decl.asInstanceOf[LocalVar] else body_graph_analysis.heap_vertex.localVar
            val arg_decl: LocalVarDecl = LocalVarDecl(arg_var.name, arg_var.typ)(arg_var.pos)
            if (!arg_vars.contains(arg_decl)) {
              reportError(ConsistencyError(s"Only argument variables can be influencing the return variable. ${arg_decl.name} may not be an argument variable.", v.pos))
            }
            influenced_graph.addEdge(method_vars(arg_decl), target_decl, new DefaultEdge)
          })

      }

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


      /** ignore the edges from the .init_ret to the ret vertex since before the method there is no init value of a return variable. */
      method.formalReturns.foreach(r => {
        body_graph.removeAllEdges(method_vars(r), r)
      })

      /** the set of all incoming edges to the return variables of the method body graph should be a subset of the set of the incoming edges of the influenced by graph */
      (method.formalReturns ++ Seq(heap_vert)).foreach(r => {
        body_graph.incomingEdgesOf(r).forEach(e => {
          if (!influenced_graph.containsEdge(body_graph.getEdgeSource(e), body_graph.getEdgeTarget(e))) {
            val ret_sources: String = body_graph.incomingEdgesOf(r).asScala.map(e => body_graph.getEdgeSource(e).name).toSet.mkString(", ").replace(".init_", "").replace(".", "")
            reportError(ConsistencyError("influenced by expression may be incorrect. Possible influenced by expression: \n" + "influenced " + r.name.replace(".", "") + " by {" + ret_sources + "}", influenced_by_pos(r)))
          }
        })
      })
    })
  }
}
