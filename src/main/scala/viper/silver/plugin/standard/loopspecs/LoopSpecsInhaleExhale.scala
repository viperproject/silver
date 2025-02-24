package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.{Bool, ErrTrafo, Exhale, Exp, If, Inhale, Label, LabelledOld, LocalVar, LocalVarAssign, LocalVarDecl, MakeTrafoPair, Method, MethodCall, NewStmt, NoInfo, NoPosition, NoTrafos, Node, NodeTrafo, Program, Seqn, Stmt, TrueLit, Type, While}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.plugin.standard.termination.transformation.ProgramManager
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.verifier.errors.ExhaleFailed

import scala.collection.mutable



//todo refactor code that is common to botth classes

class LoopSpecsInhaleExhale(loopSpecsPlugin: LoopSpecsPlugin, val program : Program) extends ProgramManager{

  def beforeVerify(): Program = {
    // For each loopspecs
    // Identify components of loop
    // Map entire loop to new code 1. inhalexhale 2. rec
    // Return program before ++ new code ++ program after



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


    def mapLoopSpecs(ls : LoopSpecs): (Seqn, Iterable[(Type, String)]) = {



      // added test case: variable scoping, see if finds targets correcctly, declare + assign, don't declare, don't assign...

      //We use distinct to not count twice a var declared oustide and then used in body plus ghost resp.


      val targets: Seq[LocalVar] = ls.writtenVars.intersect(ls.undeclLocalVars)


      //types = types ++ targets.map(_.typ)


      val prefix = "" //"__" //  "__plugin_loopspecs_"

      val known_targets : mutable.HashMap[String, String] = mutable.HashMap[String, String]()

      val known_labels : mutable.HashMap[String, String] = mutable.HashMap[String, String]()

      val known_havoc : mutable.HashMap[(Type, String), (Type, String)] = mutable.HashMap[(Type, String), (Type, String)]()

      def get_label(label: String): String =
        known_labels.getOrElseUpdate(label, uniqueName(label))

      def get_name(full_name: String): String =
        known_targets.getOrElseUpdate(full_name, uniqueName(full_name))

      def get_havoc_name(typ : Type, havocType: String): String =
        known_havoc.getOrElseUpdate((typ, havocType), (typ, uniqueName(havocType)))._2


      def get_var_name(label: String = "", name : String): String = {
        val original_str = s"$prefix${if (label != "") get_label(label) else ""}_${name}"
        get_name(original_str)

      }

      def get_var(label: String, name : String, typ : Type): LocalVar = {
        LocalVar(get_var_name(label, name), typ)()
      }

      def declare_targets_with_label(label : String): Seq[LocalVarDecl] =
        targets.map(t => {
          LocalVarDecl(get_var_name(label, t.name), t.typ)()
        })
      //Resolution via name (not ref)
      def copy_targets_with_label(label : String): Seq[Stmt] =
        targets.map(t => {
          LocalVarAssign(get_var(label, t.name, t.typ), t)()
        }) // This can never fail, simple assignment

      def checkpoint(label : String): Seq[Stmt] =
        Seq(Label(get_label(label), Seq())()) ++
          copy_targets_with_label(label)


      def call_havoc_type(typ : Type, targets : Seq[LocalVar]): Stmt = {
        MethodCall(
          get_havoc_name(typ, s"havoc_${typ}"),
          Seq(),
          targets
        )(NoPosition, NoInfo, NoTrafos)
      }


      def havoc_targets(): Seq[Stmt] =
        targets.map(t  => {
          call_havoc_type(t.typ, Seq(t))
        })

      // s"__plugin_loopspecs_{$name}_{$t.name}" = copy at label name
      // Only put a labelled old outside but could also nest them (doesn't change anything)
      // pre(list(pre(curr))) == pre(list(curr))
      // pre(accu)
      // post, ghost, basecase

      def pre_desugar_preexp(e : Exp, label : String): Exp = {

        e.transform({
          // only rename targets inside pre

          case l: LocalVar if targets.contains(l) =>
            LocalVar(get_var_name(label, l.name), l.typ)(l.pos, l.info, NodeTrafo(l)) // gets the original vars not the copies

          case pre : PreExp => // We only desugared the first pre, further nested pres are simply removed
            pre_desugar_preexp(pre.exp, label)
        })
      }

      def pre_desugar[T <: Node](node : T, label : String): T = {
        node.transform({
          // Even if this was simply a pre around a local var, having a labelled old won't hurt the soundness.
          case pre : PreExp => LabelledOld(pre_desugar_preexp(pre.exp, label), label)(pre.pos, pre.info, NodeTrafo(pre))
        })
      }

      // Exhale all loop preconditions

      // From exhale failed to precondition failed on entry

      val check_pre: Seq[Stmt] = {
        Seq(Exhale(ls.pres)(ls.pres.pos, ls.pres.info, MakeTrafoPair(ls.pres.errT, ErrTrafo({
          case ExhaleFailed(offNode, reason, cached) =>
            PreconditionNotEstablished(offNode, reason, cached)
        }))))
      }

      // Declare a non-deterministic Boolean variable
      val non_det =
        LocalVarDecl(get_var_name(name="nondet"), Bool)()

      // Common inhalations of preconditions
      val common_to_both_steps: Seq[Stmt] =
        Seq(Inhale(ls.pres)()) ++ //This can fail but will produce a contract not wellformed err which is what we want
          checkpoint("pre_iteration") // works


      // Errors:
      // -targets done
      // -pre() in right positions done
      // -check better error messages (make new errors ids to be able to check them) done
      // -post works for base not ind, same for precondition, done
      // -try ghost code failure (wrong fold)
      // -same for basecase


      // Inductive step statements
      val inductive_step: Seq[Stmt] =
        Seq(ls.body) ++
          checkpoint("after_iteration") ++
          Seq(Exhale(ls.pres)(ls.pres.pos, ls.pres.info, MakeTrafoPair(ls.pres.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              //todo does reason.offNode do the same??
              PreconditionNotPreserved(offNode, reason, cached)
          })))) ++
          havoc_targets() ++ // always works
          Seq(Inhale(pre_desugar(ls.posts, "after_iteration"))()) ++
          ls.ghost.toSeq.map(s => pre_desugar(s, "pre_iteration")) ++
          Seq(Exhale(pre_desugar(ls.posts, "pre_iteration"))(ls.posts.pos, ls.posts.info, MakeTrafoPair(ls.posts.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PostconditionNotPreservedInductiveStep(offNode, reason, cached)
          }))))
      // [postcondition.not.preserved.inductive.step:insufficient.permission]

      // Base step statements
      val base_step: Seq[Stmt] =
        ls.basecase.toSeq.map(s => pre_desugar(s, "pre_iteration")) ++
          Seq(Exhale(pre_desugar(ls.posts, "pre_iteration"))(ls.posts.pos, ls.posts.info, MakeTrafoPair(ls.posts.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PostconditionNotPreservedBaseCase(offNode, reason, cached)
          }))))

      // Caller's postconditions
      val callers_post: Seq[Stmt] =
        Seq(Inhale(pre_desugar(ls.posts, "pre_loop"))())

      val thn : Seqn =
        Seqn(Seq(
          While(TrueLit()(),
            Seq(), // No invariants
            Seqn(
              common_to_both_steps ++
                Seq(
                  If(ls.cond,
                    Seqn(inductive_step,
                      declare_targets_with_label("after_iteration"))(),
                    Seqn(base_step,
                      Seq())()
                  )()
                ), declare_targets_with_label("pre_iteration")
            )()
          )()
        ),
          Seq())()

      val els : Seqn =
        Seqn(callers_post,
          Seq())()

      // Construct the transformed sequence
      val desugared_loop =
        Seqn(
        checkpoint("pre_loop") ++ // always works
          check_pre ++ // exhale failed -> precond not established
          havoc_targets() ++ // always works
          Seq(
            If(non_det.localVar,
              thn,
              els
            )()
          ),
        Seq(non_det) ++ declare_targets_with_label("pre_loop")
      )()
      (desugared_loop, known_havoc.values)
    }
    //inside the seqs of the seqn you have the var decl

    var havoc_methods : Seq[Method] = Seq()
    //same as call transform
    val newProgram: Program = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        val (tsf_loop, havocs) = mapLoopSpecs(ls)

        havoc_methods = havoc_methods ++ havocs.map(f =>
          Method(f._2,
            Seq(),
            Seq(LocalVarDecl("x", f._1)()),
            Seq(),
            Seq(),
            None)())
        tsf_loop

    }).execute(program)
    // This is just traversal not verif

    // Check entire program for pre() that are left
    // There should be no pres. Must be user mistake.

    newProgram.transform({
      case p@PreExp(exp) =>
        reportError(ConsistencyError("Found pre expression in wrong part of program. Please only use it in a while loop's postcondition, ghostcode or base case code.", p.pos));
        exp})


    // for each type from targets add the havoc methods
    val transformedMethods = newProgram.methods ++ havoc_methods
    val finalProgram = newProgram.copy(methods = transformedMethods)(NoPosition, NoInfo, NoTrafos)
    val errs = finalProgram.check //Check again because the desugared program could clash with the outer scope or be wrong on its own

    errs.foreach(reportError(_))

    finalProgram
  }
  def reportError(error: AbstractError): Unit = {
    loopSpecsPlugin.reportError(error)
  }

}
