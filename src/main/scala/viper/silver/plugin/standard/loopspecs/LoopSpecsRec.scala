package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.{Bool, ErrTrafo, Exhale, Exp, If, Implies, Inhale, Label, LabelledOld, LocalVar, LocalVarAssign, LocalVarDecl, MakeTrafoPair, Method, MethodCall, NewStmt, NoInfo, NoPosition, NoTrafos, Node, NodeTrafo, Not, Old, Program, Seqn, Stmt, TrueLit, Type, While}
import viper.silver.verifier.errors.{ExhaleFailed, PostconditionViolated, PreconditionInCallFalse}
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.plugin.standard.termination.transformation.ProgramManager
import scala.+:

class LoopSpecsRec(loopSpecsPlugin: LoopSpecsPlugin, val program : Program) extends ProgramManager {
  val helper_method_name = "HELPER_" //Todo get name of englobing method?
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


    def mapLoopSpecs(ls : LoopSpecs): (Node, Method) = {

      def vars_from_exp(e : Exp): Set[LocalVar] = {
        var vars_read : Set[LocalVar] = Set()
        e.transform({
          case lv : LocalVar => {
            vars_read = vars_read + lv //or change
            lv
          }
        })
        vars_read
      }

      def vars_from_seqn(seqn: Seqn): Set[LocalVar] = {
        // All local variable names declared in *this* Seqn (the current scope).
        val declaredInThisScope: Set[String] =
          seqn.scopedDecls.collect { case v: LocalVarDecl => v.name }.toSet

        // All local variables read in *this* Seqn (excluding nested Seqn).
        // That means we only look at direct statements in seqn.ss.
        var vars_read : Set[LocalVar] = Set()
        seqn.ss.map({
            case LocalVarAssign(_, rhs) =>
              // Only collect vars from the RHS, since LHS is a write
              vars_read ++= vars_from_exp(rhs)

            case MethodCall(_, args, _) =>
              // Only collect from the arguments, since the "targets" are writes
              args.foreach(e => vars_read ++= vars_from_exp(e))

            case nested: Seqn =>

            case other : Node =>
              // Default: transform the statement to collect LocalVar usage, ignoring LHS if applicable.
              // This will pick up read references from any expressions inside 'other'.
              other.transform( {
                case e: Exp =>
                  vars_read ++= vars_from_exp(e)
                  e
                case se : Seq[Exp] =>
                  vars_read = vars_read ++ se.flatMap(e => vars_from_exp(e))
                  se
              })

          }
        ) //target read plus vars read

        val assignedInThisScope: Set[String] = seqn.ss.flatMap {
          case LocalVarAssign(lhs, _) => Some(lhs)
          case NewStmt(lhs, _)        => Some(lhs)
          case MethodCall(_, _, targets) => targets
          case _ => None
        }.map(_.name).toSet

        // Recursively collect assigned variables in any nested Seqn statements.
        // We do recursion *after* collecting from this scope,
        // because child scopes may declare new variables that overshadow (or should not leak out).
        val assignedFromSubSeqns: Set[String] = Set()

        /*seqn.ss.collect {
          case nested: Seqn =>
            // Recursively get targets from the nested scope
            targets_from_seqn(nested)
        }.flatten.map(_.name).toSet
*/


        // Recursively collect assigned variables in any nested Seqn statements.
        // We do recursion *after* collecting from this scope,
        // because child scopes may declare new variables that overshadow (or should not leak out).
        val readFromSubSeqns: Set[LocalVar] = seqn.ss.collect {
          case nested: Seqn =>
            // Recursively get targets from the nested scope
            vars_from_seqn(nested)
        }.flatten.toSet

        // Combine local assigned variables with the ones from sub-sequences
        val combined : Set[LocalVar] = vars_read ++ readFromSubSeqns

        // Filter out the variables that were declared in this very scope.
        // They should *not* bubble up to the parent scope's "undeclared" or external declarations.
        // declaredfromsubseqns would not be licit syntax
        combined.filterNot(lv => declaredInThisScope.contains(lv.name))
          .filterNot(lv => assignedInThisScope.contains(lv.name))
        .filterNot(lv => assignedFromSubSeqns.contains(lv.name))
      }


      // TODO: tsf error as such "  [0] Exhale might fail. There might be insufficient permission to access List(curr) (filter.vpr@47.14--47.24)"
      //  into " Precondition might fail." or the specific part of where it happened.
      //  also: complains on precondition ==> point to actual part of loop (entry start, inductive case, basecase) and same for post(ind, base)


      // added test case: variable scoping, see if finds targets correcctly, declare + assign, don't declare, don't assign...

      //We use distinct to not count twice a var declared oustide and then used in body plus ghost resp.
      //decl out, assigned in
      // so we take all the assigned in and intersect with the decl out
      val targets: Seq[LocalVar] = ls.writtenVars.intersect(ls.undeclLocalVars)
      //should be fine as we can't declare targets in pre/post so visting them shouldn't be wrong

      /*
      (
        ls.basecase.map(targets_from_seqn).getOrElse(Seq()) ++
          ls.ghost.map(targets_from_seqn).getOrElse(Seq()) ++
          targets_from_seqn(ls.body)
        ).distinctBy(_.name)
       */

      // decl out, read in, not assigned in
      val vars: Seq[LocalVar] = ls.undeclLocalVars.diff(targets)
        /*(
        ls.basecase.map(vars_from_seqn).getOrElse(Seq()) ++
          ls.ghost.map(vars_from_seqn).getOrElse(Seq()) ++
          vars_from_seqn(ls.body)
          ++ ls.pres.flatMap(vars_from_exp)
          ++ ls.posts.flatMap(vars_from_exp)
        ).toSeq.filterNot(lv => targets.contains(lv)) //probably no need for this then*/
//TODO also add cond

      def get_init_target(name : String, typ : Type): LocalVar =
        LocalVar(s"${name}_init", typ)()


      //todo: add tests for failures along the way.
      //todo: or if it verifies but shouldn't
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
          case pre : PreExp => Old(pre_desugar_preexp(pre.exp))(pre.pos, pre.info, NodeTrafo(pre))

          case l: LocalVar if forceChange && targets.contains(l) =>
            LocalVar(s"${l.name}_init", l.typ)(l.pos, l.info, NodeTrafo(l)) //todo verify if NodeTrafo necessary here but prob yes because we want the old node not the initnode
        })//NodeTrafo(l)
      }

      val assign_targets : Seq[Stmt] =
        targets.map(t => {
          LocalVarAssign(t, get_init_target(t.name, t.typ))() //target := target_init
    })

      val unique_name = uniqueName(helper_method_name)
      val unique_name_basecase = uniqueName(helper_method_name + "basecase")

      val args = (vars ++ targets) //.distinctBy(_.name)

      val inductiveStep : Seq[Stmt] =
        Seq(ls.body) ++
          Seq(MethodCall(unique_name, args, targets)(NoPosition, NoInfo, ErrTrafo({
            case PreconditionInCallFalse(offNode, reason, cached) =>
              PreconditionNotPreservedWhileLoop(offNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT), reason, cached)

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
      val args_method = (targets_init ++ lv_to_lvd(vars)) //. distinctBy(_.name.dropRight(5))

      val targets_lvd = lv_to_lvd(targets)


      val helper_method = Method(
        unique_name,
        args_method,
        targets_lvd,
        ls.pres.map(pre =>  //pre_desugar(pre, forceChange = true).withMeta(pre.pos, pre.info,pre.errT)),
          pre_desugar(pre, forceChange = true)), // can only refer to init targets (args names were changed), vars are kept the same
        //TODO. replace all with this .+ or MakeTrafoPair
        ls.posts.map(post => Implies(TrueLit()(), pre_desugar(post))(post.pos, post.info, post.errT.+(ErrTrafo({
          case PostconditionViolated(offNode, member, reason, cached) => //todo use member??
            PostconditionNotPreservedInductiveStep(offNode, reason, cached)
        })))),
        //TODO is this the best way to change the errT, plus fix error message that now includes this true ==> ...
        Some(body_inductiveStep))()

//todo add this to method decl of program if not useless
      val helper_method_basecase = Method(
        unique_name_basecase,
        args_method,
        targets_lvd,
        ls.pres.map(pre =>  //pre_desugar(pre, forceChange = true).withMeta(pre.pos, pre.info,pre.errT)),
          pre_desugar(pre, forceChange = true)), // can only refer to init targets (args names were changed), vars are kept the same
        //TODO. replace all with this .+ or MakeTrafoPair
        ls.posts.map(post => Implies(TrueLit()(), pre_desugar(post))(post.pos, post.info, post.errT.+(ErrTrafo({
          case PostconditionViolated(offNode, member, reason, cached) => //todo use member??
            PostconditionNotPreservedBaseCase(offNode, reason, cached)
        })))),
        //TODO is this the best way to change the errT, plus fix error message that now includes this true ==> ...
        Some(body_basecase))()

      //TODO: vars = read not written inside loop

      (Seqn(
        Seq(MethodCall(unique_name, args, targets)(NoPosition, NoInfo, ErrTrafo({
          case PreconditionInCallFalse(offNode, reason, cached) => //PreconditionInCallFalse(offNode, reason, cached)
            PreconditionNotEstablishedWhileLoop(
              offNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT)
             , reason, cached) //todo change to og precond not establ wihtout whiel loop
        }))) //args, targets//needs vars + targets for args
        , Seq())(), helper_method)


    }
    //inside the seqs of the seqn you have the var decl


    //same as call transform
    var helper_methods : Seq[Method] = Seq()
    val newProgram: Program = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        {

          val (n, hm) = mapLoopSpecs(ls)
          helper_methods = helper_methods ++  Seq(hm)
          n
        }

    }).execute(program)
    // This is just traversal not verif
    //TODO: test with nested loops (TD /BU) test


    val transformedMethods = newProgram.methods ++ helper_methods
    val finalProgram : Program =
      newProgram.copy(methods = transformedMethods)(NoPosition, NoInfo, NoTrafos)

    // Check entire program for pre() that are left
    // There should be no pres. Must be user mistake.

    finalProgram.transform({
      case p@PreExp(exp) =>
        reportError(ConsistencyError("Found pre expression in wrong part of program. Please only use it in a while loop's postcondition, ghostcode or base case code.", p.pos));
        exp})

    finalProgram

  }
  def reportError(error: AbstractError): Unit = {
    loopSpecsPlugin.reportError(error)
  }



}
