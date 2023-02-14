package viper.silver.plugin.standard.reasoning


import fastparse._
import org.jgrapht.Graph
import org.jgrapht.graph.{DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.utility.{Expressions, ViperStrategy}
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser._
import viper.silver.plugin.standard.reasoning.analysis.{VarAnalysisGraph, VarAnalysisSet}
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier._

import scala.annotation.unused
import scala.collection.mutable
import scala.jdk.CollectionConverters._

class ReasoningPlugin(@unused reporter: viper.silver.reporter.Reporter,
                      @unused logger: ch.qos.logback.classic.Logger,
                      @unused config: viper.silver.frontend.SilFrontendConfig,
                      fp: FastParser) extends SilverPlugin with ParserPluginTemplate with VarAnalysisSet {

  import fp.{FP, ParserExtension, block, exp, idndef, idnuse, keyword, trigger, typ}


  override def reportErrorWithMsg(error: AbstractError): Unit = reportError(error)

  /** Parser for existential elimination statements. */
  def existential_elim[_: P]: P[PExistentialElim] = {
    FP(keyword("obtain") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ keyword("where") ~/ trigger.rep ~/ exp).map { case (pos, (varList, t, e)) => PExistentialElim(varList.map { case (id, typ) => PLocalVarDecl(id, typ, None)(e.pos) }, t, e)(pos) }

  }

  /** Parser for universal introduction statements. */
  def universal_intro[_: P]: P[PUniversalIntro] =
    FP(keyword("prove") ~/ keyword("forall") ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ trigger.rep(sep = ",") ~/ keyword("assuming") ~/ exp ~/ keyword("implies") ~/ exp ~/ block).map { case (pos, (varList, triggers, e1, e2, b)) => PUniversalIntro(varList.map { case (id, typ) => PLocalVarDecl(id, typ, None)(e1.pos) }, triggers, e1, e2, b)(pos) }

  /** Parser for new influence by condition */
  def influenced_by[_: P]: P[PFlowAnnotation] =
  //FP(keyword("influenced") ~/ (idndef ~ ":" ~ typ) ~/ keyword("by") ~ "{" ~/ (idndef ~ ":" ~ typ).rep(sep = ",") ~/ "}").map { case (pos, (v_idndef, v_typ, varList)) => PFlowAnalysis(v_idndef,v_typ, varList.map { case (id, typ) => (id, typ)})(pos)}
  //FP(keyword("influenced") ~/ (idnuse) ~/ keyword("by") ~ "{" ~/ (idnuse).rep(sep = ",") ~/ "}").map { case (pos, (v_idnuse, varList)) => PFlowAnalysis(v_idnuse, varList)(pos) }
    P(keyword("influenced") ~/ (influenced_by_var | influenced_by_heap))

  def influenced_by_var[_: P]: P[PFlowAnnotation] = {
    FP(idnuse ~/ keyword("by") ~ "{" ~/ (heap_then_vars | vars_then_opt_heap) ~/ "}").map {
      case (pos, (v_idnuse: PExp, (varList: Seq[PExp], None))) =>
        PFlowAnnotationVar(v_idnuse, varList)(pos)
      case (pos, (v_idnuse: PExp, varList: Option[Seq[PExp]])) =>
        PFlowAnnotationVarHeapArg(v_idnuse, varList.getOrElse(Seq()))(pos)
      case (pos, (v_idnuse: PExp, (varList1: Seq[PExp], varList2: Some[Seq[PExp]]))) =>
        PFlowAnnotationVarHeapArg(v_idnuse, varList1 ++ varList2.getOrElse(Seq()))(pos)
    }
  }

  def vars_then_opt_heap[_: P]: P[(Seq[PExp], Option[Seq[PExp]])] = {
    P(idnuse.rep(sep = ",") ~/ ("," ~/ keyword("heap") ~/ ("," ~/ idnuse.rep(sep = ",")).?).?.map {
      /** If there is no heap keyword */
      case None => None

      /** If there is the heap keyword but no further variables */
      case Some(None) => Some(Seq())

      /** If there is the heap keyword and additionally further variables */
      case Some(Some(varList)) => Some(varList)

    })
  }

  def heap_then_vars[_: P]: P[Option[Seq[PExp]]] = {
    P(keyword("heap") ~/ ("," ~/ idnuse.rep(sep = ",")).?)
  }

  def influenced_by_heap[_: P]: P[PFlowAnnotation] = {
    FP(keyword("heap") ~/ keyword("by") ~ "{" ~/ (heap_then_vars | vars_then_opt_heap) ~/ "}").map {
      case (pos, (varList: Seq[PExp], None)) =>
        reportError(ParseError("The heap should always be influenced by the heap.", SourcePosition(pos._1.file,pos._1,pos._2)))
        PFlowAnnotationHeap(varList)(pos)
      case (pos, varList: Option[Seq[PExp]]) =>
        PFlowAnnotationHeapHeapArg(varList.getOrElse(Seq()))(pos)
      case (pos, (varList1: Seq[PExp], varList2: Some[Seq[PExp]])) =>
        PFlowAnnotationHeapHeapArg(varList1 ++ varList2.getOrElse(Seq()))(pos)
    }
  }

  /** Add existential elimination and universal introduction to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String]("obtain", "where", "prove", "forall", "assuming", "implies"))
    ParserExtension.addNewKeywords(Set[String]("influenced", "by", "heap"))
    ParserExtension.addNewStmtAtEnd(existential_elim(_))
    ParserExtension.addNewStmtAtEnd(universal_intro(_))
    // Add new parser to the precondition
    /** doesn't work because of return value in precondition? */
    //ParserExtension.addNewPreCondition(influenced_by(_))
    // Add new parser to the postcondition
    ParserExtension.addNewPostCondition(influenced_by(_))
    input
  }


  override def beforeVerify(input: Program): Program = {
    val usedNames: mutable.Set[String] = collection.mutable.Set(input.transitiveScopedDecls.map(_.name): _*)

    def uniqueName(name: String): String = {
      var i = 1
      var newName = name
      while (usedNames.contains(newName)) {
        newName = name + i
        i += 1
      }
      usedNames.add(newName)
      newName
    }

    def substituteWithFreshVars[E <: Exp](vars: Seq[LocalVarDecl], exp: E): (Seq[(LocalVarDecl, LocalVarDecl)], E) = {
      val declMapping = vars.map(oldDecl =>
        oldDecl -> LocalVarDecl(uniqueName(oldDecl.name), oldDecl.typ)(oldDecl.pos, oldDecl.info, oldDecl.errT))
      val transformedExp = applySubstitution(declMapping, exp)
      (declMapping, transformedExp)
    }

    def applySubstitution[E <: Exp](mapping: Seq[(LocalVarDecl, LocalVarDecl)], exp: E): E = {
      Expressions.instantiateVariables(exp, mapping.map(_._1.localVar), mapping.map(_._2.localVar))
    }

    /** check that influenced by expressions are exact or overapproximate the body of the method. */
    val body_graph_analysis: VarAnalysisGraph = VarAnalysisGraph(input, reportError)
    input.methods.foreach(method => {

      val init_args_decl = method.formalArgs.map(a => body_graph_analysis.createInitialVertex(a))
      val init_rets_decl = method.formalReturns.map(r => body_graph_analysis.createInitialVertex(r))
      val method_vars: Map[LocalVarDecl, LocalVarDecl] = ((method.formalArgs zip init_args_decl) ++ (method.formalReturns zip init_rets_decl) ++ Seq((body_graph_analysis.heap_vertex, body_graph_analysis.createInitialVertex(body_graph_analysis.heap_vertex)))).toMap
      val empty_body_graph = body_graph_analysis.createEmptyGraph(method_vars)
      val body_graph = body_graph_analysis.compute_graph(empty_body_graph, method.body.getOrElse(Seqn(Seq(), Seq())()), method_vars)
      //println("method body graph: " + body_graph_analysis.createDOT(body_graph))

      val influenced_graph = body_graph_analysis.copyGraph(empty_body_graph)
      method.posts.foreach {
        case v@(FlowAnnotationVar(_, _) | FlowAnnotationVarHeapArg(_, _)) =>
          val (target, args) = v match {
            case FlowAnnotationVar(t, a) =>
              (t, a)
            case FlowAnnotationVarHeapArg(t, a) =>
              (t, a ++ Seq(body_graph_analysis.heap_vertex.localVar))
          }

          val target_var: LocalVar = target.asInstanceOf[LocalVar]
          val target_decl: LocalVarDecl = LocalVarDecl(target_var.name, target_var.typ)(target_var.pos)
          args.foreach(arg => {
            val arg_var: LocalVar = arg.asInstanceOf[LocalVar]
            val arg_decl: LocalVarDecl = LocalVarDecl(arg_var.name, arg_var.typ)(arg_var.pos)
            influenced_graph.addEdge(method_vars(arg_decl), target_decl, new DefaultEdge)
          })
        case h@(FlowAnnotationHeap(_) | FlowAnnotationHeapHeapArg(_)) =>
          val args = h match {
            case FlowAnnotationHeap(a) =>
              a
            case FlowAnnotationHeapHeapArg(a) =>
              a ++ Seq(body_graph_analysis.heap_vertex.localVar)
          }
          args.foreach(arg => {
            val arg_var: LocalVar = arg.asInstanceOf[LocalVar]
            val arg_decl: LocalVarDecl = LocalVarDecl(arg_var.name, arg_var.typ)(arg_var.pos)
            influenced_graph.addEdge(method_vars(arg_decl), body_graph_analysis.heap_vertex, new DefaultEdge)
          })
      }


      /** ignore the edges from the .init_ret to the ret vertex since before the method there is no init value of a return variable. */
      method.formalReturns.foreach(r => {
        body_graph.removeAllEdges(method_vars(r), r)
      })

      /** the set of all incoming edges to the return variables of the method body graph should be a subset of the set of the incoming edges of the influenced by graph */
      method.formalReturns.foreach(r => {
        body_graph.incomingEdgesOf(r).forEach(e => {
          if (!influenced_graph.containsEdge(body_graph.getEdgeSource(e), body_graph.getEdgeTarget(e))) {
            val ret_sources: String = body_graph.incomingEdgesOf(r).asScala.map(e => body_graph.getEdgeSource(e).name).toSet.mkString(", ").replace(".init_", "").replace(".", "")
            reportError(ConsistencyError("influenced by expression may be incorrect. Possible influenced by expression: \n" + "influenced " + r.name.replace(".", "") + " by {" + ret_sources + "}", r.pos))
          }
        })
      })
    })


    ViperStrategy.Slim({
      case e@ExistentialElim(v, trigs, exp) => // e = ExistentialElim(vardecl, exp)
        val (new_v_map, new_exp) = substituteWithFreshVars(v, exp)
        val new_trigs = trigs.map(t => Trigger(t.exps.map(e1 => applySubstitution(new_v_map, e1)))(t.pos))
        Seqn(
          Seq(
            Assert(Exists(new_v_map.map(_._2), new_trigs, new_exp)(e.pos, ReasoningInfo))(e.pos)
          )
            ++
            v.map(variable => LocalVarDeclStmt(variable)(variable.pos)) //list of variables
            ++
            Seq(
              Inhale(exp)(e.pos)
            ),
          Seq()
        )(e.pos)

      /** remove the influenced by postconditions. */
      case m: Method =>
        var postconds: Seq[Exp] = Seq()
        m.posts.foreach {
          case _: FlowAnnotation =>
            postconds = postconds
          case s@_ =>
            postconds = postconds ++ Seq(s)
        }
        val newMethod =
          if (postconds != m.posts) {
            m.copy(pres = m.pres, posts = postconds)(m.pos, m.info, m.errT)
          } else {
            m
          }
        newMethod

      case u@UniversalIntro(v, trigs, exp1, exp2, blk) =>
        val boolvar = LocalVarDecl(uniqueName("b"), Bool)(exp1.pos)

        /** check whether immutable universal introduction variables are reassigned
          * if non empty set returned, immutable variables contained in there might have been reassigned. */
        /*
        val reassigned = check_is_reassigned(v,blk)
        if (reassigned.nonEmpty) {
          val reassigned_names: String = reassigned.mkString(", ")
          val reassigned_pos: String = reassigned.map(_.pos).mkString(", ")
          reportError(ConsistencyError("Universal Introduction variable(s) (" + reassigned_names + ") might have been reassigned at position(s) (" + reassigned_pos + ")", u.pos))
        }
         */


        /**
          * get all variables that are assigned to inside the block and take intersection with universal introduction
          * variables. If they are contained throw error since these variables should be immutable
          */
        val written_vars: Option[Set[LocalVarDecl]] = writtenTo(blk)
        if (written_vars.isDefined) {
          val reassigned_vars: Set[LocalVarDecl] = written_vars.get.intersect(v.toSet)
          if (reassigned_vars.nonEmpty) {
            val reassigned_names: String = reassigned_vars.mkString(", ")
            val reassigned_pos: String = reassigned_vars.map(_.pos).mkString(", ")
            reportError(ConsistencyError("Universal Introduction variable(s) (" + reassigned_names + ") might have been reassigned at position(s) (" + reassigned_pos + ")", u.pos))
          }
        }


        val vars_outside_blk: mutable.Set[Declaration] = mutable.Set()

        /** Get all variables that are in scope in the current method but not inside the block */
        input.methods.foreach(m => m.body.get.ss.foreach(s => {
          if (s.contains(u)) {
            vars_outside_blk ++= mutable.Set(m.transitiveScopedDecls: _*)
          }
        }))
        /** Variables declared in the universal introduction statement are tainted */
        val tainted: Set[LocalVarDecl] = v.toSet

        /*
        /**
          * SET VERSION
          */
        /** check whether any additional variables are tainted inside of the block */
        var all_tainted = Set[Declaration]()
        all_tainted = get_tainted_vars_stmt(tainted, blk)


        /** remove the variables that were tainted to begin with */
        vars_outside_blk --= mutable.Set(u.transitiveScopedDecls: _*)

        /** check whether any variables were tainted that are declared outside of our block */
        if (!(vars_outside_blk.intersect(all_tainted).isEmpty)) {
          val tainted_vars: Set[Declaration] = all_tainted.intersect(vars_outside_blk)
          val problem_vars: String = tainted_vars.mkString(", ")
          val problem_pos: String = tainted_vars.map(vs => vs.pos).mkString(", ")
          reportError(ConsistencyError("Universal introduction variable might have been assigned to variable " + problem_vars + " at positions (" + problem_pos + "), defined outside of the block", u.pos))
        }
        */

        /**
          * GRAPH VERSION
          */

        val graph_analysis: VarAnalysisGraph = VarAnalysisGraph(input, reportError)

        /** create graph with vars that are in scope */
        vars_outside_blk --= mutable.Set(u.transitiveScopedDecls: _*)
        vars_outside_blk ++= v
        var graph: Graph[LocalVarDecl, DefaultEdge] = new DefaultDirectedGraph[LocalVarDecl, DefaultEdge](classOf[DefaultEdge])

        /** old graph */
        //vars_outside_blk.foreach(v => graph.addVertex(v))

        /** new graph */

        var allVertices: Map[LocalVarDecl, LocalVarDecl] = Map[LocalVarDecl, LocalVarDecl]()
        /*
        var allVertices: Set[(LocalVarDecl, LocalVarDecl)] = Set()
        */
        /** add heap variables to vertices */
        allVertices += (graph_analysis.heap_vertex -> graph_analysis.createInitialVertex(graph_analysis.heap_vertex))

        vars_outside_blk.foreach(v => {
          val v_decl = v.asInstanceOf[LocalVarDecl]
          val v_init = graph_analysis.createInitialVertex(v_decl)
          allVertices += (v_decl -> v_init)
          /*
          allVertices = allVertices + ((v_init,v_decl))
           */
          graph.addVertex(v_init)
          graph.addVertex(v_decl)
        })
        //println(allVertices)
        //println("first graph:")
        //println(createDOT(graph))
        /** old graph */
        //graph = compute_graph(graph, blk)

        /** new graph */
        //println("ReasoningPlugin initial graph:", graph)
        /*
        graph = compute_graph(graph, blk, allVertices)
         */

        graph = graph_analysis.compute_graph(graph, blk, allVertices)

        //for debugging
        //println("ReasoningPlugin final Graph")
        //println(graph_analysis.createDOT(graph))

        var noEdges: Boolean = true
        var badEdges = Set[DefaultEdge]()
        tainted.foreach(v => {
          if (graph.edgesOf(graph_analysis.createInitialVertex(v)).size() > 1) {
            badEdges = badEdges ++ graph.edgesOf(graph_analysis.createInitialVertex(v)).asScala.toSet[DefaultEdge]
            noEdges = false
          }
          //noEdges = noEdges && graph.edgesOf(createInitialVertex(v)).size() <= 1
        })
        if (!noEdges) {
          //println("entered not empty thingy")
          var tainted_vars: Set[LocalVarDecl] = Set()
          //graph.edgeSet().forEach(e => {
          badEdges.foreach(e => {
            //println("edge inside:", e)
            val target = graph.getEdgeTarget(e)
            if (!tainted.contains(target)) {
              tainted_vars = tainted_vars + graph.getEdgeTarget(e)
            }
          })
          val problem_vars: String = tainted_vars.mkString(", ")
          val problem_pos: String = tainted_vars.map(vs => vs.pos).mkString(", ")
          reportError(ConsistencyError("Universal introduction variable might have been assigned to variable " + problem_vars + " at positions (" + problem_pos + "), defined outside of the block", u.pos))
        }


        val (new_v_map, new_exp1) = substituteWithFreshVars(v, exp1)
        val new_exp2 = applySubstitution(new_v_map, exp2)
        val arb_vars = new_v_map.map(vars => vars._2)
        val new_trigs = trigs.map(t => Trigger(t.exps.map(e1 => applySubstitution(new_v_map, e1)))(t.pos))
        // label should also be in used Names => can also use uniqueName function
        val lbl = uniqueName("l")


        Seqn(
          Seq(
            Label(lbl, Seq())(u.pos),
            If(boolvar.localVar,
              Seqn(
                Seq(
                  Inhale(exp1)(exp1.pos)
                ),
                Seq())(exp1.pos),
              Seqn(Seq(), Seq())(exp1.pos)

            )(exp1.pos),
            blk,
            Assert(Implies(boolvar.localVar, exp2)(exp2.pos))(exp2.pos),
            Inhale(Forall(arb_vars, new_trigs, Implies(LabelledOld(new_exp1, lbl)(exp2.pos), new_exp2)(exp2.pos))(exp2.pos))(exp2.pos)
          ),
          Seq(boolvar) ++ v
        )(exp1.pos)

    }, Traverse.TopDown).execute(input)
  }


  /*
  override def mapVerificationResult(input: VerificationResult): VerificationResult = {
    val errors: Seq[AbstractError] = input match {
      case Success => Seq()
      case Failure(errors) =>
        errors.map {
          case af@AssertFailed(a, err_reason, c) =>
            if (a.info == ExistentialElim) {
              ExistentialElimFailed(a, err_reason, c)
            }
            else if (a.info == UniversalIntro) {
              UniversalIntroFailed(a, err_reason, c)
            } else if ((a.info == FlowAnnotationVar) || (a.info == FlowAnnotationHeap) || a.info == FlowAnnotationVarHeapArg || a.info == FlowAnnotationHeapHeapArg) {
              FlowAnalysisFailed(a, err_reason, c)
            } else {
              af
            }

        }
    }
    if (errors.length == 0) Success
    else Failure(errors)
  }
   */
}