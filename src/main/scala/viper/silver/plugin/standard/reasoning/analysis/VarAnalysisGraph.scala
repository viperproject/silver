package viper.silver.plugin.standard.reasoning.analysis

import org.jgrapht.Graph
import org.jgrapht.graph.{AbstractBaseGraph, DefaultDirectedGraph, DefaultEdge}
import viper.silver.ast.{AccessPredicate, Apply, Assert, Assume, BinExp, CurrentPerm, DomainFuncApp, Exhale, Exp, FieldAccess, FieldAssign, Fold, ForPerm, FuncApp, Goto, If, Inhale, Int, Label, LocalVar, LocalVarAssign, LocalVarDecl, MethodCall, Package, Perm, Program, Ref, Seqn, Stmt, UnExp, Unfold, While}
import viper.silver.plugin.standard.reasoning.{FlowAnnotation, OldCall, Var}
//import viper.silver.plugin.standard.reasoning.{ExistentialElim, FlowAnnotationHeap, FlowAnnotationHeapHeapArg, FlowAnnotationVar, FlowAnnotationVarHeapArg, UniversalIntro}
import viper.silver.plugin.standard.reasoning.{ExistentialElim, UniversalIntro}

import viper.silver.verifier.{AbstractError, ConsistencyError}

import java.io.StringWriter
import scala.jdk.CollectionConverters._
import scala.util.control.Breaks.break



case class VarAnalysisGraph(prog: Program,
                            reportErrorWithMsg: AbstractError => Unit) {

  val prefix: String = ".init_"

  val heap_vertex: LocalVarDecl = LocalVarDecl(".heap", Ref)()


  def executeTaintedGraphAnalysis(graph1: Graph[LocalVarDecl,DefaultEdge], tainted: Set[LocalVarDecl], blk: Seqn, allVertices: Map[LocalVarDecl, LocalVarDecl], u: UniversalIntro): Unit = {


    val graph = compute_graph(graph1, blk, allVertices)


    var noEdges: Boolean = true
    var badEdges = Set[DefaultEdge]()
    tainted.foreach(v => {
      if (graph.edgesOf(createInitialVertex(v)).size() > 1) {
        badEdges = badEdges ++ graph.edgesOf(createInitialVertex(v)).asScala.toSet[DefaultEdge]
        noEdges = false
      }
    })
    if (!noEdges) {
      var tainted_vars: Set[LocalVarDecl] = Set()
      badEdges.foreach(e => {
        val target = graph.getEdgeTarget(e)
        if (!tainted.contains(target)) {
          tainted_vars = tainted_vars + graph.getEdgeTarget(e)
        }
      })
      val problem_vars: String = tainted_vars.mkString(", ")
      val problem_pos: String = tainted_vars.map(vs => vs.pos).mkString(", ")
      reportErrorWithMsg(ConsistencyError("Universal introduction variable might have been assigned to variable " + problem_vars + " at positions (" + problem_pos + "), defined outside of the block", u.pos))
    }
  }


  /**
    * Creates the Vertex that represents the initial value of the variable before the statement is executed
    * @param variable Variable for which we want to create the Vertex which represents the initial value of the variable
    * @return a LocalVariableDeclaration
    */
  def createInitialVertex(variable:LocalVarDecl): LocalVarDecl = {
    LocalVarDecl(prefix + variable.name, variable.typ)(variable.pos)
  }

  /**
    * creates a graph with no edges and only the vertices
    * @param vertices represent the variables that are in scope
    * @return an graph with only vertices
    */
  def createEmptyGraph(vertices: Map[LocalVarDecl,LocalVarDecl]): Graph[LocalVarDecl, DefaultEdge] = {
    val graph: Graph[LocalVarDecl,DefaultEdge]  = new DefaultDirectedGraph[LocalVarDecl,DefaultEdge](classOf[DefaultEdge])
    for ((v,v_init)<-vertices) {
      graph.addVertex(v_init)
      graph.addVertex(v)
    }
    graph
  }


  /**
    * create a Graph that contains all the vertices with an edge from edge vertex representing the initial value of the variable to the 'end'-value of the variable
    * @param vertices represent the variables that are in scope
    * @return an identity graph
    */
  def createIdentityGraph(vertices: Map[LocalVarDecl,LocalVarDecl]): Graph[LocalVarDecl, DefaultEdge] = {
    val graph: Graph[LocalVarDecl, DefaultEdge] = createEmptyGraph(vertices)
    for ((v,v_init)<-vertices) {
      graph.addEdge(v_init, v)
    }
    graph
  }

  /**
    * add Edges from the vertices representing the initial value to the vertices representing its 'end'-values if they have no incoming edge yet
    * @param graph existing graph
    * @param vertices the vertices representing variables which should be checked
    * @return graph
    */
  def addMissingEdges(graph: Graph[LocalVarDecl,DefaultEdge], vertices:Map[LocalVarDecl,LocalVarDecl]): Graph[LocalVarDecl, DefaultEdge] = {

    for ((v,v_init)<-vertices) {
      if (graph.incomingEdgesOf(v).isEmpty) {
        graph.addEdge(v_init, v, new DefaultEdge)
      }
    }
    graph
  }

  /**
    * @param graph graph that should be translated to DOT-language
    * @return String that is the graph in DOT-language
    *
    */
  def createDOT(graph: Graph[LocalVarDecl, DefaultEdge]): String = {
    val writer: StringWriter = new StringWriter()
    writer.write("strict digraph G {\n")
    graph.vertexSet().forEach(v => {
      writer.write("  " + v.name.replace(".","") + ";\n")
    })
    graph.edgeSet().forEach(e => {
      writer.write("  " + graph.getEdgeSource(e).name.replace(".","") + " -> " + graph.getEdgeTarget(e).name.replace(".","") + ";\n")
    })
    writer.write("}\n")
    writer.toString
  }

  /**
    * returns all the variables inside an expression
    * @param graph existing graph
    * @param exp   expressions from which all variables should be returned
    * @return set of Variable declarations
    */
  def getVarsFromExpr(graph: Graph[LocalVarDecl, DefaultEdge], exp: Exp): Set[LocalVarDecl] = {
    val vars: Set[LocalVarDecl] = Set()
    exp match {
      case l@LocalVar(_, _) =>
        var l_decl: LocalVarDecl = LocalVarDecl("", Int)()
        graph.vertexSet().forEach(v => if (v.name == l.name) {
          l_decl = v
        })
        if (l_decl.name == "") {
          l_decl = LocalVarDecl(l.name, l.typ)()
        }
        vars + l_decl

      case BinExp(exp1, exp2) =>
        getVarsFromExpr(graph, exp1) ++ getVarsFromExpr(graph, exp2)

      case UnExp(exp) =>
        getVarsFromExpr(graph, exp)

      case FuncApp(_,exps) =>
        var allVars = vars
        if (!vars.contains(heap_vertex)) {
          allVars += heap_vertex
        }
        exps.foreach(e => {
          val exp_vars = getVarsFromExpr(graph, e)
          exp_vars.foreach(v => {
            if (v.typ != Ref) {
              allVars += v
            }
          })
        })
        allVars

      case DomainFuncApp(_,exps,_) =>
        var allVars = vars
        exps.foreach(e => {
          val exp_vars = getVarsFromExpr(graph, e)
          exp_vars.foreach(v => {
            allVars += v
          })
        })
        allVars

      case _: ForPerm | _: CurrentPerm =>
        if (!vars.contains(heap_vertex)) {
          vars + heap_vertex
        } else {
          vars
        }


      case FieldAccess(v,_) =>
        getVarsFromExpr(graph, v)

      case AccessPredicate(access, _) =>
        /** Should only be the case in e.g.an inhale or an exhale statement */
        var allVars = vars
        val access_vars = getVarsFromExpr(graph, access)
        access_vars.foreach(v => {
          allVars += v
        })
        allVars

      case _ =>
        Set()
    }
  }

  /**
    * returns a shallow copy of graph instance, neither Vertices nor Edges are cloned
    * @param graph graph that should be copied.
    * @return copied graph
    */
  def copyGraph(graph: Graph[LocalVarDecl, DefaultEdge]): Graph[LocalVarDecl, DefaultEdge] = {
    val copied_graph = graph.asInstanceOf[AbstractBaseGraph[LocalVarDecl, DefaultEdge]].clone().asInstanceOf[DefaultDirectedGraph[LocalVarDecl, DefaultEdge]]
    copied_graph
  }

  /**
    * takes to graphs and returns a new graph containing the union of the edges of both input graphs. Both graphs should contain the same vertices!
    * @param graph1
    * @param graph2
    * @return graph
    */
  def unionEdges(graph1: Graph[LocalVarDecl, DefaultEdge], graph2: Graph[LocalVarDecl, DefaultEdge]): Graph[LocalVarDecl,DefaultEdge] = {
    val new_graph = copyGraph(graph1)
    if (graph1.vertexSet().equals(graph2.vertexSet())) {
      for (e2: DefaultEdge <- graph2.edgeSet().asScala.toSet) {
        if (!new_graph.containsEdge(e2)) {
          val src = graph2.getEdgeSource(e2)
          val trgt = graph2.getEdgeTarget(e2)
          new_graph.addEdge(src, trgt, e2)
        }
      }
    } else {
      /** TODO: Should error be thrown? Should not happen */
    }
    new_graph
  }

  /**
    * merges two graphs. Meaning: we create a new graph with all the init vertices from graph one and all 'end' vertices from graph two.
    * We assume that all 'end' vertices from graph1 can be matched with an init vertex from graph2. E.g. v = .init_v
    * We then add an edge from a to b if there is a path from a to b.
    * @param graph1
    * @param graph2
    * @param vertices
    * @return merged graph
    */
  def mergeGraphs(graph1: Graph[LocalVarDecl, DefaultEdge], graph2: Graph[LocalVarDecl, DefaultEdge], vertices: Map[LocalVarDecl, LocalVarDecl]): Graph[LocalVarDecl,DefaultEdge] = {
    val new_graph = createEmptyGraph(vertices)
    for (e1: DefaultEdge <- graph1.edgeSet().asScala.toSet) {
      val src = graph1.getEdgeSource(e1)
      val trgt = graph1.getEdgeTarget(e1)
      val init_trgt = vertices.get(trgt)
      if (init_trgt.isDefined) {
        for (e2: DefaultEdge <- graph2.outgoingEdgesOf(init_trgt.get).asScala.toSet) {
          new_graph.addEdge(src, graph2.getEdgeTarget(e2), new DefaultEdge)
        }
      } else {
        /** TODO: Should technically not happen */
      }
    }
    new_graph
  }



  def compute_graph(graph: Graph[LocalVarDecl,DefaultEdge], stmt: Stmt, vertices: Map[LocalVarDecl,LocalVarDecl]): Graph[LocalVarDecl,DefaultEdge] = {
    stmt match {
      case Seqn(ss, scopedSeqnDeclarations) =>
        var allVertices: Map[LocalVarDecl,LocalVarDecl] = vertices
        for (d <- scopedSeqnDeclarations) {
          if (d.isInstanceOf[LocalVarDecl]) {
            val d_decl = d.asInstanceOf[LocalVarDecl]
            val d_init = createInitialVertex(d_decl)
            allVertices += (d_decl -> d_init)
          }
        }
        var new_graph: Graph[LocalVarDecl, DefaultEdge] = createIdentityGraph(allVertices)
        for (s <- ss) {
          val graph_copy = copyGraph(new_graph)
          val comp_graph = compute_graph(graph_copy, s, allVertices)

          new_graph = mergeGraphs(new_graph, comp_graph, allVertices)
        }

        val final_graph: Graph[LocalVarDecl, DefaultEdge] = createEmptyGraph(vertices)
        new_graph.edgeSet().forEach(e => {
          val source: LocalVarDecl = new_graph.getEdgeSource(e)
          val target: LocalVarDecl = new_graph.getEdgeTarget(e)
          if (final_graph.containsVertex(source) && final_graph.containsVertex(target)) {
            final_graph.addEdge(source, target, e)
          }
        })
        final_graph

      case If(cond, thn, els) =>
        val id_graph = createIdentityGraph(vertices)
        val expr_vars = getVarsFromExpr(id_graph, cond)
        val cond_graph = copyGraph(id_graph)
        val thn_graph = compute_graph(copyGraph(id_graph), thn, vertices)
        val els_graph = compute_graph(copyGraph(id_graph), els, vertices)
        val writtenToThn = writtenTo(vertices, thn).getOrElse(Set())
        val writtenToEls = writtenTo(vertices, els).getOrElse(Set())
        val allWrittenTo = writtenToThn ++ writtenToEls
        for (w <- allWrittenTo) {
          if (cond_graph.containsVertex(w)) {
            for (v <- expr_vars) {
              val v_init = vertices(v)
              cond_graph.addEdge(v_init, w, new DefaultEdge)
            }
          }
        }
        writtenToThn.intersect(writtenToEls).foreach(v => {
          cond_graph.removeEdge(vertices(v),v)
        })
        val thn_els_graph = unionEdges(thn_graph, els_graph)
        val res_graph = unionEdges(cond_graph, thn_els_graph)
        res_graph

      case w@While(cond, _, body) =>
        val graph_copy: Graph[LocalVarDecl, DefaultEdge] = copyGraph(graph)

        /** analyse one iteration of the while loop */
        var new_graph: Graph[LocalVarDecl, DefaultEdge] = compute_graph(graph_copy, If(cond, body, Seqn(Seq(), Seq())(body.pos))(body.pos), vertices)
        new_graph = mergeGraphs(graph_copy, new_graph, vertices)

        /** check whether the edges are equal.
          * First check whether both edge sets have the same size
          * then go through each edge and check whether it also exists in the new graph */
        var edges_equal: Boolean = true
        val equal_size: Boolean = graph.edgeSet().size().equals(new_graph.edgeSet().size())
        if (equal_size && new_graph.vertexSet().equals(graph.vertexSet())) {
          for (e1: DefaultEdge <- new_graph.edgeSet().asScala.toSet) {
            if (graph.getEdge(new_graph.getEdgeSource(e1), new_graph.getEdgeTarget(e1)) == null) {
              edges_equal = false
              compute_graph(new_graph, w, vertices)
              break()
            }
          }
          graph
        } else {
          compute_graph(new_graph, w, vertices)
        }

      case LocalVarAssign(lhs,rhs) =>
        var new_graph: Graph[LocalVarDecl,DefaultEdge] = createEmptyGraph(vertices)
        val rhs_vars = getVarsFromExpr(new_graph, rhs)
        val lhs_decl: LocalVarDecl = LocalVarDecl(lhs.name,lhs.typ)(lhs.pos)

        for (v <- rhs_vars) {
          /** if the variable on the right hand side is a field access */
          if (v.equals(heap_vertex)) {
            val heap_init = vertices(heap_vertex)
            new_graph.addEdge(heap_init, lhs_decl, new DefaultEdge)
          } else {
            val v_init = vertices(v)
            new_graph.addEdge(v_init, lhs_decl, new DefaultEdge)
          }
        }

        /** Since variables that are not assigned to should have an edge from their initial value to their 'end'-value */
        val vert_wout_lhs = vertices - lhs_decl
        new_graph = addMissingEdges(new_graph, vert_wout_lhs)
        new_graph

      case Inhale(exp) => expInfluencesAll(exp, graph, vertices)
        /*
        val id_graph = createIdentityGraph(vertices)
        val inhale_vars = getVarsFromExpr(graph, exp)
        inhale_vars.foreach(v => {
          //val init_v = createInitialVertex(v)
          val init_v = vertices(v)

          //id_graph.addEdge(init_v, heap_vertex, new DefaultEdge)
          vertices.keySet.foreach(k => {
            id_graph.addEdge(init_v, k, new DefaultEdge)
            println(s"edge from ${init_v} to ${k}")
          })

        })
        id_graph
         */


      /** same as inhale */
      case Assume(exp) => expInfluencesAll(exp, graph, vertices)

      case Exhale(exp) =>
        val id_graph = createIdentityGraph(vertices)
        if (exp.isPure) {
          graph
        } else {
          val exhale_vars = getVarsFromExpr(graph, exp)
          exhale_vars.foreach(v => {
            if (v.typ == Ref) {
              val init_v = createInitialVertex(v)
              id_graph.addEdge(init_v, heap_vertex, new DefaultEdge)
            }
          })
          id_graph
        }



      case Label(_, _) =>
        graph

      case MethodCall(methodName, args, targets) =>
      val met = prog.findMethod(methodName)
        /** create graph from each variable in each expression to the according method variable */
        val methodcall_graph: Graph[LocalVarDecl, DefaultEdge] = createEmptyGraph(vertices)

        createInfluencedByGraph(methodcall_graph,vertices,args,targets,met.formalArgs, met.formalReturns,met.posts)


      case FieldAssign(_, rhs) =>
        val id_graph = createIdentityGraph(vertices)
        val rhs_vars = getVarsFromExpr(graph, rhs)
        rhs_vars.foreach(v => {
          /** Edge from .init_heap to heap does not have to be added since it exists anyways */
          if (v.equals(heap_vertex)) {
            id_graph
          } else {
            val v_init = createInitialVertex(v)
            id_graph.addEdge(v_init, heap_vertex, new DefaultEdge)
          }
        })
        id_graph

      case ExistentialElim(_,_,_) => graph

      case UniversalIntro(varList,_,_,_,blk) =>
        val new_vertices: Map[LocalVarDecl, LocalVarDecl] = vertices ++ varList.map(v => (v -> createInitialVertex(v)))
        val new_graph = compute_graph(graph,blk,new_vertices)
        varList.foreach(v => {
          new_graph.removeVertex(v)
          new_graph.removeVertex(new_vertices(v))
        })
        new_graph

      case Assert(_) => graph

      case Fold(acc) =>
        val id_graph = createIdentityGraph(vertices)
        val vars = getVarsFromExpr(graph, acc)
        vars.foreach(v => {
          id_graph.addEdge(vertices(v), heap_vertex, new DefaultEdge)
        })
        id_graph

      case Unfold(acc) =>
        val id_graph = createIdentityGraph(vertices)
        val vars = getVarsFromExpr(graph, acc)
        vars.foreach(v => {
          id_graph.addEdge(vertices(v), heap_vertex, new DefaultEdge)
        })
        id_graph

      case Apply(exp) =>
        val id_graph = createIdentityGraph(vertices)
        val vars = getVarsFromExpr(graph, exp)
        vars.foreach(v => {
          id_graph.addEdge(vertices(v), heap_vertex, new DefaultEdge)
        })
        id_graph

      case Package(wand, _) =>
        val id_graph = createIdentityGraph(vertices)
        val vars = getVarsFromExpr(graph, wand)
        vars.foreach(v => {
          id_graph.addEdge(vertices(v), heap_vertex, new DefaultEdge)
        })
        id_graph

      case g@Goto(_) =>
        reportErrorWithMsg(ConsistencyError(s"${g} is an undefined statement for the universal introduction block", g.pos))
        graph

      case OldCall(_,_) => graph
      case s@_ =>
        reportErrorWithMsg(ConsistencyError(s"${s} is an undefined statement for the universal introduction block", s.pos))
        graph
        //throw new UnsupportedOperationException("undefined statement for universal introduction block: " + s)
    }
  }

  def expInfluencesAll(exp:Exp, graph: Graph[LocalVarDecl, DefaultEdge], vertices: Map[LocalVarDecl,LocalVarDecl]) : Graph[LocalVarDecl, DefaultEdge] = {
    val id_graph = createIdentityGraph(vertices)
    val inhale_vars = getVarsFromExpr(graph, exp)
    inhale_vars.foreach(v => {
      //val init_v = createInitialVertex(v)
      val init_v = vertices(v)

      //id_graph.addEdge(init_v, heap_vertex, new DefaultEdge)
      vertices.keySet.foreach(k => {
        id_graph.addEdge(init_v, k, new DefaultEdge)
      })

    })
    id_graph
  }

  def createInfluencedByGraph(graph: Graph[LocalVarDecl, DefaultEdge], vertices: Map[LocalVarDecl,LocalVarDecl], arg_names: Seq[Exp], ret_names: Seq[LocalVar], method_arg_names: Seq[LocalVarDecl], method_ret_names: Seq[LocalVarDecl],  posts: Seq[Exp]): Graph[LocalVarDecl, DefaultEdge] = {
    /** set of all target variables that have not been included in the influenced by expression up until now */
    var retSet: Set[LocalVarDecl] = method_ret_names.toSet + heap_vertex
    var methodcall_graph = copyGraph(graph)
    val method_arg_names_incl_heap = method_arg_names ++ Seq(heap_vertex)

    /** create .arg_ declaration for each argument */
    var method_args: Map[LocalVarDecl, LocalVarDecl] = Map()
    var method_arg_counter: Int = 0
    method_arg_names_incl_heap.foreach(method_arg => {
      method_args += (method_arg -> LocalVarDecl(".arg" + method_arg_counter, method_arg.typ)(method_arg.pos))
      method_arg_counter += 1
    })

    /** create .ret_ declaration for each return variable */
    var method_rets: Map[LocalVarDecl, LocalVarDecl] = Map()
    var method_ret_counter: Int = 0
    retSet.foreach(method_ret => {
      method_rets += (method_ret -> LocalVarDecl(".ret" + method_ret_counter, method_ret.typ)(method_ret.pos))
      method_ret_counter += 1
    })

    /** contains all variables that are passed to the method */
    var total_arg_decls: Set[LocalVarDecl] = Set(heap_vertex)

    /** add edges from method arguments to .arg variables */
    (arg_names zip method_arg_names).foreach(arg => {
      /** extract all variables in expressions that are added to the method */
      val arg_decls: Set[LocalVarDecl] = getVarsFromExpr(graph, arg._1)
      total_arg_decls ++= arg_decls
      arg_decls.foreach(arg_decl => {
        if (!methodcall_graph.containsVertex(vertices(arg_decl))) {
          methodcall_graph.addVertex(vertices(arg_decl))
        }
        if (!methodcall_graph.containsVertex(method_args(arg._2))) {
          methodcall_graph.addVertex(method_args(arg._2))
        }
        /** add edge from .init variable to .arg variable */
        methodcall_graph.addEdge(vertices(arg_decl), method_args(arg._2))
      })
    })

    /** add heap and corresponding .arg variable as method argument */
    if(!methodcall_graph.containsVertex(heap_vertex)) {
      methodcall_graph.addVertex(vertices(heap_vertex))
    }
    if(!methodcall_graph.containsVertex(method_args(heap_vertex))) {
      methodcall_graph.addVertex(method_args(heap_vertex))
    }
    methodcall_graph.addEdge(vertices(heap_vertex),method_args(heap_vertex))


    /** need to add the edges from the influenced by expression */
    posts.foreach {
      case FlowAnnotation(returned, arguments) =>

        /** returned has to be instance of LocalVar */
        val returned_var: LocalVar = if (returned.isInstanceOf[Var]) returned.asInstanceOf[Var].var_decl.asInstanceOf[LocalVar] else heap_vertex.localVar
        /** create LocalVarDecl such that it can be added in the graph */
        val return_decl = LocalVarDecl(returned_var.name, returned_var.typ)(returned_var.pos)
        retSet -= return_decl

        if (!methodcall_graph.containsVertex(method_rets(return_decl))) {
          methodcall_graph.addVertex(method_rets(return_decl))
        }

        arguments.foreach(argument => {
          /** argument has to be instance of LocalVar */
          val argument_var: LocalVar = if (argument.isInstanceOf[Var]) argument.asInstanceOf[Var].var_decl.asInstanceOf[LocalVar] else heap_vertex.localVar
          val argument_decl = LocalVarDecl(argument_var.name, argument_var.typ)(argument_var.pos)
          /** get corresponding .arg variable and add edge from .arg to .ret vertex */
          val prov_decl = method_args(argument_decl)
          methodcall_graph.addEdge(prov_decl, method_rets(return_decl), new DefaultEdge)
        })

    }

    /** now need to add to graph the edges from the method return variables to the target variables */
    val targets_decl: Seq[LocalVarDecl] = ret_names.map(t => {
      graph.vertexSet().asScala.filter(lvd => lvd.name == t.name).head
    }) ++ Seq(heap_vertex)
    ((method_ret_names ++ Seq(heap_vertex)) zip targets_decl).foreach(ret => {
      if (!methodcall_graph.containsVertex(ret._2)) {
        methodcall_graph.addVertex(ret._2)
      }
      if (!methodcall_graph.containsVertex(method_rets(ret._1))) {
        methodcall_graph.addVertex(method_rets(ret._1))
      }
      /** add edge from .ret variable to target variable */
      methodcall_graph.addEdge(method_rets(ret._1), ret._2)
    })


    /** add edges from all method argument to each return variable that wasn't mentioned in the influenced by statement */
    retSet.foreach(r => {
      method_arg_names_incl_heap.foreach(a => {
        if (!methodcall_graph.containsVertex(method_args(a))) {
          methodcall_graph.addVertex(method_args(a))
        }
        if (!methodcall_graph.containsVertex(method_rets(r))) {
          methodcall_graph.addVertex(method_rets(r))
        }
        methodcall_graph.addEdge(method_args(a), method_rets(r), new DefaultEdge)
      })
    })


    var copy_arg_graph = copyGraph(methodcall_graph)

    /** remove edge from .ret_ vertex to the final vertex */
    for (elem <- targets_decl) {
      /** get all edges from target variables to .ret variables */
      copy_arg_graph.incomingEdgesOf(elem).forEach(inc_edge => {
        //should only be one edge
        val ret_vert = methodcall_graph.getEdgeSource(inc_edge)
        /** get edges from .ret variable to .arg variable */
        copy_arg_graph.incomingEdgesOf(ret_vert).forEach(ret_inc_e => {
          val arg_vert = methodcall_graph.getEdgeSource(ret_inc_e)
          /** add edge from .arg variable to target variable */
          methodcall_graph.addEdge(arg_vert, elem)
        })
        /** remove .ret variables */
        methodcall_graph.removeVertex(ret_vert)
      })
    }


    /** remove edge from the .arg_ to the .init vertex */
    copy_arg_graph = copyGraph(methodcall_graph)
    /** go through .init variables */
    for (elem <- total_arg_decls + heap_vertex) {
      /** go through all outgoing edges of .init variable */
      copy_arg_graph.outgoingEdgesOf(vertices(elem)).forEach(out_edge => {
        /** get the .arg variable that edge leads to */
        val arg_vert = methodcall_graph.getEdgeTarget(out_edge)
        /** get edges from .arg variable to the target variable */
        copy_arg_graph.outgoingEdgesOf(arg_vert).forEach(arg_out_e => {
          val final_vert = methodcall_graph.getEdgeTarget(arg_out_e)
          /** create edge from .init variable to target variable */
          methodcall_graph.addEdge(vertices(elem), final_vert)
        })
        methodcall_graph.removeVertex(arg_vert)
      })
    }

    /** Since variables that are not assigned to should have an edge from their initial value to their 'end'-value */
    val vert_wout_lhs = vertices.removedAll(targets_decl)
    methodcall_graph = addMissingEdges(methodcall_graph, vert_wout_lhs)
    methodcall_graph
  }


  def writtenTo(vertices: Map[LocalVarDecl,LocalVarDecl], stmt: Stmt): Option[Set[LocalVarDecl]] = {
    var output: Option[Set[LocalVarDecl]] = None
    stmt match {
      case Seqn(ss, _) =>
        for (s <- ss) {
          output match {
            case None => output = writtenTo(vertices, s)
            case Some(v) => output = Some(v ++ writtenTo(vertices, s).getOrElse(Set[LocalVarDecl]()))
          }

        }
        output
      case LocalVarAssign(lhs, _) =>
        var res: Option[Set[LocalVarDecl]] = None
        for (vs <- vertices) {
          if (vs._1.name == lhs.name) {
            res = Some(Set(vs._1))
          } else {
            /** This is the case if the variable is in scope in e.g. a then or an else block. */
            res = Some(Set(LocalVarDecl(lhs.name, lhs.typ)(lhs.pos)))
          }
        }
        res
      case If(_, thn, els) =>
        val writtenThn: Option[Set[LocalVarDecl]] = writtenTo(vertices, thn)
        val writtenEls: Option[Set[LocalVarDecl]] = writtenTo(vertices, els)
        (writtenThn, writtenEls) match {
          case (None, None) => None
          case (Some(_), None) => writtenThn
          case (None, Some(_)) => writtenEls
          case (Some(t), Some(e)) => Some(t ++ e)
        }

      case While(_, _, body) =>
        writtenTo(vertices, body)

      case MethodCall(_, _, _) =>
        None


      case Inhale(_) =>
        None

      case Assume(_) =>
        None

      case Label(_, _) =>
        None

      case _ =>
        None
    }
  }

 
}


/**
  * ************************************
  *                                    *
  *         old Graph version          *
  *                                    *
  * ************************************
  */
/*
trait VarAnalysisGraph {
  def reportErrorWithMsg(error: AbstractError): Unit

  /**
    *
    * @param graph to which vertices should be added
    * @param scopedSeqnDeclarations variable declaration inside this codeblock
    * @return graph with the newly added vertices
    */
  def addNodes(graph: Graph[Declaration, DefaultEdge], scopedSeqnDeclarations: Seq[Declaration]): Graph[Declaration, DefaultEdge] = {
    val result_graph: Graph[Declaration, DefaultEdge] = graph
    scopedSeqnDeclarations.foreach(decl => result_graph.addVertex(decl))
    result_graph
  }

  /**
    * @param graph
    * @return String that is the graph in DOT-language
    *
    */

  def createDOT(graph:Graph[Declaration, DefaultEdge]) : String = {
    val writer: StringWriter = new StringWriter()
    writer.write("strict digraph G {\n")
    graph.vertexSet().forEach(v => {
      writer.write("  " + v.name + ";\n")
    })
    graph.edgeSet().forEach(e => {
      writer.write("  " + graph.getEdgeSource(e) + " -> " + graph.getEdgeTarget(e) + ";\n")
    })
    writer.write("}\n")
    writer.toString
  }

  /**
    *
    * @param graph existing graph
    * @param exp expressions from which all variables should be returned
    * @return set of Variable declarations
    */
  def getVarsFromExpr(graph: Graph[Declaration, DefaultEdge], exp: Exp): Set[Declaration] = {
    val vars: Set[Declaration] = Set()
    exp match {
      case l@LocalVar(_, _) => {
        var l_decl: Declaration = LocalVarDecl("", Int)()
        graph.vertexSet().forEach(v => if (v.name == l.name) { l_decl = v })
        if (l_decl.name == "") {
          l_decl = LocalVarDecl(l.name,l.typ)()
        }
        vars + l_decl
      }
      case BinExp(exp1, exp2) => {
        getVarsFromExpr(graph, exp1) ++ getVarsFromExpr(graph, exp2)
      }
      case UnExp(exp) => {
        getVarsFromExpr(graph, exp)
      }
      case _ => Set()
    }
  }

  /**
    *
    * @param graph graph that should be copied. Note: Shallow copy of graph instance, neither Vertices nor Edges are cloned
    * @return copied graph
    */
  def copyGraph(graph: Graph[Declaration, DefaultEdge]): Graph[Declaration, DefaultEdge] = {
    val copied_graph = graph.asInstanceOf[AbstractBaseGraph[Declaration,DefaultEdge]].clone().asInstanceOf[DefaultDirectedGraph[Declaration, DefaultEdge]]
    copied_graph
  }

  /**
    *
    * @param graph
    * @param src src vertex of edge (basically righthand-side of the assignment
    * @param target target vertex of edge (basically lefthand-side of the assigment
    * @return Graph with the new edge included
    */
  def addTransitiveEdge(graph: Graph[Declaration, DefaultEdge], src: Declaration, target: Declaration): Graph[Declaration, DefaultEdge] = {
    val new_graph = copyGraph(graph)
    // the first condition depends on whether or not we want to include self loops
    if (/*!src.equals(target) && */!new_graph.containsEdge(src, target)) {
      new_graph.addEdge(src, target, new DefaultEdge)
      /** go on level up and add those edges as well, this is enough
        * since our invariant tells us that our graph is always transitively closed */
      new_graph.incomingEdgesOf(src).forEach(e => {
        val src1 = new_graph.getEdgeSource(e)
        /** edge only needs to be added if it doesn't exist yet */
        if (!new_graph.containsEdge(src1, target)) {
          new_graph.addEdge(src1, target, new DefaultEdge)
        }
      })
    }
    new_graph
  }

  def compute_graph(graph: Graph[Declaration, DefaultEdge], stmt: Stmt): Graph[Declaration, DefaultEdge] = {
    stmt match {
      case Seqn(ss, scopedSeqnDeclarations) => {
        val graph_copy: Graph[Declaration, DefaultEdge] = copyGraph(graph)
        var new_graph = addNodes(graph_copy, scopedSeqnDeclarations)
        for (s <- ss) {
          val new_graph_copy: Graph[Declaration,DefaultEdge] = copyGraph(new_graph)
          new_graph = compute_graph(new_graph_copy, s)
        }
        val final_graph: Graph[Declaration, DefaultEdge] = new DefaultDirectedGraph[Declaration, DefaultEdge](classOf[DefaultEdge])
        graph.vertexSet().forEach(v => final_graph.addVertex(v))
        new_graph.edgeSet().forEach(e => {
          val source: Declaration = new_graph.getEdgeSource(e)
          val target: Declaration = new_graph.getEdgeTarget(e)
          if (final_graph.containsVertex(source) && final_graph.containsVertex(target)) {
            final_graph.addEdge(source, target, e)
          }
        })
        final_graph
      }

      case If(cond, thn, els) => {
        val cond_variables = getVarsFromExpr(graph, cond)
        val new_graph = copyGraph(graph)

        val new_graph_for_els: Graph[Declaration,DefaultEdge] = copyGraph(new_graph)
        val thn_graph = compute_graph(new_graph, thn)
        val els_graph = compute_graph(new_graph_for_els, els)

        //println("then graph: ", createDOT(thn_graph))
        //println("else graph: ", createDOT(els_graph))


        /** take union of these two graphs from the else and the then block
          * First: make copy of thn_graph and declare this as the graph_union
          * Second: add all edges from els_graph that are not in the graph_union yet */
        var graph_union: Graph[Declaration,DefaultEdge] = copyGraph(thn_graph)
        els_graph.edgeSet().forEach(e => {
          if (!graph_union.containsEdge(e)) {
            graph_union.addEdge(els_graph.getEdgeSource(e), els_graph.getEdgeTarget(e), e)
          }
        })

        cond_variables.foreach(src => {
          val writtenToThn = writtenTo(new_graph, thn)
          val writtenToEls = writtenTo(new_graph, els)
          val allWrittenTo = writtenToThn.getOrElse(Set()) ++ writtenToEls.getOrElse(Set())
          allWrittenTo.foreach(t => {
            /** otherwise it is an assigment to a variable that is only inside
              * the scope of the block and therefore not relevant for us
              */
            if (graph_union.containsVertex(t)) {
              /** we need here transitive edge since otherwise the invariant may not hold (graph is transitively closed) */
              graph_union = addTransitiveEdge(graph_union, src, t)
              // graph_union.addEdge(src, t, new DefaultEdge)
            }
          })
        })
        graph_union
      }

      case w@While(cond, _, body) => {
        val graph_copy : Graph[Declaration,DefaultEdge] = copyGraph(graph)
        /** analyse one iteration of the while loop */
        val new_graph: Graph[Declaration, DefaultEdge] = compute_graph(graph_copy, If(cond,body,Seqn(Seq(), Seq())(body.pos))(body.pos))
        //println("graph")
        //println(createDOT(graph))
        println("new_graph")
        println(createDOT(new_graph))

        /** check whether the edges are equal.
          * First check whether both edge sets have the same size
          * then go through each edge and check whether it also exists in the new graph*/
        var edges_equal: Boolean = graph.edgeSet().size().equals(new_graph.edgeSet().size())
        if (edges_equal) {
          for (e1: DefaultEdge <- new_graph.edgeSet().asScala.toSet) {
            edges_equal = false
            for (e2: DefaultEdge <- graph.edgeSet().asScala.toSet) {
              edges_equal = edges_equal || e1.equals(e2)
            }
            /** if no equal edge found then break out of the loop */
            if (!edges_equal) {
              break()
            }
          }
        }
        if (new_graph.vertexSet().equals(graph.vertexSet()) && edges_equal) {
          graph
        } else {
          compute_graph(new_graph, w)
        }
      }

      case LocalVarAssign(lhs, rhs) => {
        val rhs_vars = getVarsFromExpr(graph, rhs)
        //var lhs_decl: Declaration = LocalVarDecl("",Int)()
        /** This way the position is the location of the assignment not the declaration. Better for error message but makes less sense I guess */
        val lhs_decl: Declaration = LocalVarDecl(lhs.name,lhs.typ)(lhs.pos)
        //graph.vertexSet().forEach(v => if (v.name == lhs.name) {lhs_decl=v})
        //println("Before assignment: ", createDOT(graph))
        var new_graph: Graph[Declaration, DefaultEdge] = copyGraph(graph)

        val incomingEdges: Set[DefaultEdge] = graph.incomingEdgesOf(lhs_decl).asScala.toSet

        val edgesToRemove: Set[DefaultEdge] = graph.edgesOf(lhs_decl).asScala.toSet

        //println("Edges to remove", lhs, rhs, edgesToRemove)
        /** remove all edges to and from the lhs in the new graph, since the lhs is reassigned */
        //println("before removing: New graph, ", createDOT(new_graph))
        edgesToRemove.foreach(e => new_graph.removeEdge(e))
        //println("after removing: New graph, ", createDOT(new_graph))


        /** add all new edges to the graph */
        rhs_vars.foreach(v => {
          /** if v not equal to the lhs then add the Transitive edge to the new_graph */
          if(!v.equals(lhs_decl)) {
              new_graph = addTransitiveEdge(new_graph, v, lhs_decl)

          /** if v is equal to the lhs then we need to add all the incoming edge to the lhs back into the new graph */
          } else {
            incomingEdges.foreach(e => new_graph.addEdge(graph.getEdgeSource(e), graph.getEdgeTarget(e),e))
          }
          //println("after adding the new edges: ",createDOT(new_graph))
        })
        //println("After assignment: ", createDOT(new_graph))

        new_graph
      }

      case i@Inhale(exp) => {
        if (exp.isPure) {
          graph
        } else {
          reportErrorWithMsg(ConsistencyError("There might be an impure inhale expression inside universal introduction block", i.pos))
          graph
        }
      }

      case Assume(_) => {
        graph
      }

      case Label(_, _) => {
        graph
      }

      /** TODO: Method call */
      case m@MethodCall(methodName, args, targets) => {
        verifier.findMethod
        reportErrorWithMsg(ConsistencyError("Might be not allowed method call inside universal introduction block", m.pos))
        /** maybe add to graph all edges from args to targets */
        /** somehow would have to check the influenced _ target _ by {...}. maybe like this?*/
        /*
        for (s<-m.subnodes) {
          if (s.isInstanceOf[PostconditionBlock]) {

          }
        }

         */
        graph
      }

      case f@FieldAssign(_, _) => {
        reportErrorWithMsg(ConsistencyError("FieldAssign for universal introduction block", f.pos))
        graph
      }

      case _ => {
        throw new UnsupportedOperationException("undefined statement for universal introduction block")
      }

    }
  }

  def writtenTo(graph: Graph[Declaration, DefaultEdge], stmt: Stmt): Option[Set[Declaration]] = {
    var output: Option[Set[Declaration]] = None
    stmt match {
      case Seqn(ss, _) => {
        for (s <- ss) {
          output match {
            case None => output = writtenTo(graph,s)
            case Some(v) => output = Some(v ++ writtenTo(graph,s).getOrElse(Set[Declaration]()))
          }

        }
        output
      }
      case LocalVarAssign(lhs, _) => {
        // val lhs_var = LocalVarDecl(lhs.name, lhs.typ)(lhs.pos)
        var lhs_decl: Declaration = LocalVarDecl("", Int)()
        graph.vertexSet().forEach(v => { if (v.name == lhs.name) { lhs_decl = v } })
        Some(Set(lhs_decl))
      }
      case If(_, thn, els) => {
        val writtenThn: Option[Set[Declaration]] = writtenTo(graph, thn)
        val writtenEls: Option[Set[Declaration]] = writtenTo(graph, els)
        (writtenThn, writtenEls) match {
          case (None, None) => None
          case (Some(_), None) => writtenThn
          case (None, Some(_)) => writtenEls
          case (Some(t), Some(e)) => Some(t ++ e)
        }
      }

      case While(_, _, body) => {
        writtenTo(graph, body)
      }

      /** TODO */
      case MethodCall(_, _, _) => {
        None
      }


      case Inhale(_) => {
        None
      }

      case Assume(_) => {
        None
      }

      case Label(_, _) => {
        None
      }

      case _ => {
        None
      }
    }
  }
  /** Own Edge class such that we can define the equals method.
    * Two edges should be equal if their source and target vertices are equal. */
  class DefaultEdge extends DefaultEdge {
    override def equals(any: Any): Boolean = {
      if(any.isInstanceOf[DefaultEdge]) {
        val other = any.asInstanceOf[DefaultEdge]
        this.getSource.equals(other.getSource) && this.getTarget.equals(other.getTarget)
      } else {
        false
      }
    }
  }

}

 */