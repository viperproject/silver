package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.{Bool, ErrTrafo, Exhale, Exp, If, Implies, Inhale, Label, LabelledOld, LocalVar, LocalVarAssign, LocalVarDecl, MakeTrafoPair, Method, MethodCall, NewStmt, NoInfo, NoPosition, NoTrafos, Node, NodeTrafo, Not, Old, Program, Seqn, Stmt, TrueLit, Type, While}
import viper.silver.verifier.errors.{ContractNotWellformed, ExhaleFailed, PostconditionViolated, PreconditionInCallFalse}
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.plugin.standard.termination.transformation.ProgramManager

import scala.+:

class LoopSpecsRec(loopSpecsPlugin: LoopSpecsPluginRec, val program : Program) extends ProgramManager {
  val helper_method_name = "HELPER_"
  def beforeVerify(): Program ={
    // For each loopspecs
    // Identify components of loop
    // Map entire loop to new code 1. inhalexhale 2. rec
    // Return input before ++ new code ++ input after



    //cond: Exp,
    //      pres: Seq[Exp],
    //      posts: Seq[Exp],
    //      body: Seqn,
    //      ghost: Option[Seqn],
    //      basecase



    //1. no assign in ghost ==> error
    //2. or we allow but then treat them <== THIS OPTION

    //copy
    //while()
    //{ ghost{var d:= 0}}
    //


    def mapLoopSpecs(ls : LoopSpecs): (Node, Method, Method) = {



      // TODO: tsf error as such "  [0] Exhale might fail. There might be insufficient permission to access List(curr) (filter.vpr@47.14--47.24)"
      //  into " Precondition might fail." or the specific part of where it happened.
      //  also: complains on precondition ==> point to actual part of loop (entry start, inductive case, basecase) and same for post(ind, base)

      //decl out, assigned in
      val targets: Seq[LocalVar] = ls.writtenVars.intersect(ls.undeclLocalVars)


      // decl out, read in, not assigned in
      val vars: Seq[LocalVar] = ls.undeclLocalVars.diff(targets)


      def get_init_target(name : String, typ : Type): LocalVar =
        LocalVar(s"${name}_init", typ)()


      def pre_desugar_preexp(e : Exp): Exp = {
        e.transform({
          // only rename targets inside pre
          case l: LocalVar if targets.contains(l) =>
            LocalVar(s"${l.name}_init", l.typ)(l.pos, l.info, NodeTrafo(l)) // gets the original vars not the copies

          case pre : PreExp => // We only desugared the first pre, further nested pres are simply removed
            pre_desugar_preexp(pre.exp)
        })
      }

      def pre_desugar[T <: Node](node : T, forceChange : Boolean = false): T = {
        node.transform({
          // Even if this was simply a pre around a local var, having a labelled old won't hurt the soundness.
          case pre : PreExp if !forceChange => Old(pre_desugar_preexp(pre.exp))(pre.pos, pre.info, NodeTrafo(pre))

          case l: LocalVar if forceChange && targets.contains(l) =>
            LocalVar(s"${l.name}_init", l.typ)(l.pos, l.info, NodeTrafo(l))
            //So the error refers to the old node and not the "_init" node
        })//NodeTrafo(l)
      }

      val assign_targets : Seq[Stmt] =
        targets.map(t => {
          LocalVarAssign(t, get_init_target(t.name, t.typ))() //target := target_init
    })

      val unique_name_inductive_step = uniqueName(helper_method_name + "inductive_step")
      val unique_name_basecase = uniqueName(helper_method_name + "basecase")

      val args = (vars ++ targets) //.distinctBy(_.name)

      val inductiveStep : Seq[Stmt] =
        Seq(ls.body) ++
          Seq(MethodCall(unique_name_inductive_step, args, targets)(NoPosition, NoInfo, ErrTrafo({
            case PreconditionInCallFalse(offNode, reason, cached) =>
              PreconditionNotPreserved(offNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT), reason, cached)

          }))) ++
          ls.ghost.toSeq.map(pre_desugar(_))
            //pre desugar

      val basecase : Seq[Stmt] =
        ls.basecase.toSeq.map(pre_desugar(_)) //todo verify


      val body_inductiveStep = Seqn(
        assign_targets ++
          Seq(
            Inhale(ls.cond)()) ++
          inductiveStep
        ,
        Seq())()

      val body_basecase = Seqn(
        assign_targets ++
          Seq(
            Inhale(Not(ls.cond)())()) ++
          basecase
        ,
        Seq())()



      def lv_to_lvd(l : Seq[LocalVar], init : Boolean = false): Seq[LocalVarDecl] ={
        val suffix = if (init) "_init" else ""
        l.map(lv => LocalVarDecl(s"${lv.name}${suffix}", lv.typ)())
      }

      val targets_init = lv_to_lvd(targets, init = true)
      val args_method = (lv_to_lvd(vars) ++ targets_init) //. distinctBy(_.name.dropRight(5))

      val targets_lvd = lv_to_lvd(targets)


      val helper_method = Method(
        unique_name_inductive_step,
        args_method,
        targets_lvd,
          //pre_desugar(pre, forceChange = true).withMeta(pre.pos, pre.info,pre.errT)),
          Seq(pre_desugar(ls.pres, forceChange = true)), // can only refer to init targets (args names were changed), vars are kept the same
        Seq(pre_desugar(ls.posts).withMeta(ls.posts.pos, ls.posts.info, ls.posts.errT.+(ErrTrafo({
          case PostconditionViolated(offNode, member, reason, cached) =>
            PostconditionNotPreservedInductiveStep(offNode, reason, cached)

//          case ContractNotWellformed(offendingNode, reason, cached) =>
//            ContractNotWellformed(offendingNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT), reason, cached)
        })))),
        Some(body_inductiveStep))()

      val helper_method_basecase = Method(
        unique_name_basecase,
        args_method,
        targets_lvd,
          //pre_desugar(pre, forceChange = true).withMeta(pre.pos, pre.info,pre.errT)),
         Seq(pre_desugar(ls.pres, forceChange = true)), // can only refer to init targets (args names were changed), vars are kept the same
        //TODO. replace all with this .+ or MakeTrafoPair
        Seq(pre_desugar(ls.posts).withMeta(ls.posts.pos, ls.posts.info, ls.posts.errT.+(ErrTrafo({
          case PostconditionViolated(offNode, member, reason, cached) =>
            PostconditionNotPreservedBaseCase(offNode, reason, cached)

//          case ContractNotWellformed(offendingNode, reason, cached) =>
//            ContractNotWellformed(offendingNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT), reason, cached)
        })))),
        Some(body_basecase))()


      val helper_method_call : Seqn =
        Seqn(
        Seq(
          MethodCall(unique_name_inductive_step, args, targets)(NoPosition, NoInfo, ErrTrafo({
          case PreconditionInCallFalse(offNode, reason, cached) => //PreconditionInCallFalse(offNode, reason, cached)
            PreconditionNotEstablished(
              offNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT)
              , reason, cached)

          }))), Seq())() //args, targets//needs vars + targets for args

      (helper_method_call, helper_method, helper_method_basecase)


    }
    //inside the seqs of the seqn you have the var decl


    //same as call transform
    var helper_methods : Seq[Method] = Seq()
    val map_loopspecs = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        {

          val (n, hm, hmbc) = mapLoopSpecs(ls)
          helper_methods = helper_methods ++  Seq(hm, hmbc)
          n
        }

    })
    // This is just traversal not verif


    var found = false
    val find_loopspecs = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        found = true
        ls
    })

    var curr_program = program
    do {
      curr_program = map_loopspecs.execute(curr_program)
      curr_program = curr_program.copy(methods = curr_program.methods ++ helper_methods)(NoPosition, NoInfo, NoTrafos)
      helper_methods = Seq()

      found = false
      find_loopspecs.execute(curr_program)
    }while(found)

    curr_program.transform({
      case p@PreExp(exp) =>
        reportError(ConsistencyError("Found pre expression in wrong part of program. Please only use it in a while loop's postcondition, ghostcode or base case code.", p.pos));
        exp})


    val errs = curr_program.check //Check again because the desugared program could clash with the outer scope or be wrong on its own

    errs.foreach(reportError(_))

   curr_program

  }
  def reportError(error: AbstractError): Unit = {
    loopSpecsPlugin.reportError(error)
  }



}
