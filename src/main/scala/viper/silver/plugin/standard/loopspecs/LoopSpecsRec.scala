package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.ast.{
  Bool, ErrTrafo, Exhale, Exp, If, Implies, Inhale, Label, LabelledOld, LocalVar,
  LocalVarAssign, LocalVarDecl, MakeTrafoPair, Method, MethodCall, NewStmt, NoInfo,
  NoPosition, NoTrafos, Node, NodeTrafo, Not, Old, Program, Seqn, Stmt, TrueLit,
  Type, While
}
import viper.silver.verifier.errors.{
  ContractNotWellformed, ExhaleFailed, PostconditionViolated, PreconditionInCallFalse
}
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.plugin.standard.termination.transformation.ProgramManager

import scala.+:

/**
 * The LoopSpecsRec class transforms annotated `while` loops into
 * recursive methods to be verified. Specifically, for each loop:
 *   1. It extracts the loop's condition, preconditions, postconditions, body, and basecase.
 *   2. It generates two helper methods:
 *      - An inductive step method that re-executes the loop body and recurses.
 *      - A base-case method that executes once the loop condition fails.
 *   3. It replaces the original `while` block with a call to the inductive-step helper.
 *
 * The transformation ensures loop preconditions (`Pre(...)`) and postconditions
 * (`Post(...)`) are respected by creating copies of "target" variables (written in the loop)
 * and carefully desugaring `pre` expressions to preserve old values.
 */
class LoopSpecsRec(loopSpecsPlugin: LoopSpecsPluginRec, val program: Program) extends ProgramManager {

  /** Prefix to identify newly generated helper methods. */
  val helper_method_name = "HELPER_"

  /**
   * Main entry point for rewriting loops with specs. It:
   *   - Traverses the AST to find LoopSpecs nodes.
   *   - For each LoopSpecs node, creates corresponding helper methods
   *     for the inductive step and the base case.
   *   - Replaces the original loop with a method call to the inductive helper.
   *   - Appends the new helper methods to the program.
   *   - Performs final consistency checks and reports errors.
   * @return A modified Program with all loop specs expanded into recursive methods.
   */
  def beforeVerify(): Program ={

    /**
     * Maps a LoopSpecs node to:
     *  1) A call to the newly generated inductive-step method.
     *  2) The inductive-step method definition itself.
     *  3) The base-case method definition.
     */
    def mapLoopSpecs(ls : LoopSpecs): (Node, Method, Method) = {

      // Identify local variables that are read/modified inside the loop.
      // We create “targets” for variables that are both written and not declared in the loop scope.
      val targets: Seq[LocalVar] = ls.writtenVars.intersect(ls.undeclLocalVars)
      val vars: Seq[LocalVar] = ls.undeclLocalVars.diff(targets)

      // Helper for generating an "_init" variable copy, used to store pre-loop values.
      def get_init_target(name : String, typ : Type): LocalVar =
        LocalVar(s"${name}_init", typ)()

      /**
       * Replaces `pre(...)` in the loop's preconditions, ghost code, or basecase
       * by references to the "_init" variables. In effect, `pre(x)` → `x_init`.
       * If we find nested `pre(...)`, we recursively desugar them as well.
       */
      def pre_desugar_preexp(e : Exp): Exp = {
        e.transform({
          // Only rename "target" variables inside `pre(...)`.
          case l: LocalVar if targets.contains(l) =>
            LocalVar(s"${l.name}_init", l.typ)(l.pos, l.info, NodeTrafo(l))

          // If we spot a nested PreExp, desugar further.
          case pre: PreExp =>
            pre_desugar_preexp(pre.exp)
        })
      }

      /**
       * Desugars `PreExp` nodes and optionally forces rewriting of local vars:
       * - forceChange indicates if we must rename every local var in `targets`
       *   to its "_init" version (used in method preconditions).
       */
      def pre_desugar[T <: Node](node : T, forceChange : Boolean = false): T = {
        node.transform({
          // The top-level `pre(...)` becomes an Old(...) to keep track of old state,
          // or we rename to `_init` if forced (i.e. in method specs).
          case pre: PreExp if !forceChange =>
            Old(pre_desugar_preexp(pre.exp))(pre.pos, pre.info, NodeTrafo(pre))

          // Force rename any local var in targets to its `_init` version.
          case l: LocalVar if forceChange && targets.contains(l) =>
            LocalVar(s"${l.name}_init", l.typ)(l.pos, l.info, NodeTrafo(l))
        })
      }

      // Generate assignments: target := target_init
      val assign_targets : Seq[Stmt] =
        targets.map(t => LocalVarAssign(t, get_init_target(t.name, t.typ))())

      // Generate unique method names for inductive step and base case.
      val unique_name_inductive_step = uniqueName(helper_method_name + "inductive_step")
      val unique_name_basecase = uniqueName(helper_method_name + "basecase")

      // The arguments to the helper methods: all "vars" plus "targets".
      val args = (vars ++ targets)

      /**
       * Inductive step body:
       *   1) Re-assign loop targets to their `_init` copies.
       *   2) Inhale the loop condition.
       *   3) Run the loop body + recurse (method call).
       *   4) (Optionally) apply the loop ghost code.
       */
      val inductiveStep : Seq[Stmt] =
        Seq(ls.body) ++
          Seq(MethodCall(unique_name_inductive_step, args, targets)(NoPosition, NoInfo, ErrTrafo({
            // Custom error mapping
            case PreconditionInCallFalse(offNode, reason, cached) =>
              PreconditionNotPreserved(offNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT), reason, cached)
          }))) ++
          ls.ghost.toSeq.map(pre_desugar(_))

      // Base case body: similarly apply base-case code once cond is false
      val basecase : Seq[Stmt] =
        ls.basecase.toSeq.map(pre_desugar(_))

      // Construct method body for the inductive step.
      // Essentially, set targets, inhale condition, run body, call self, run ghost.
      val body_inductiveStep = Seqn(
        assign_targets ++
          Seq(Inhale(ls.cond)()) ++
          inductiveStep,
        Seq())()

      // Construct method body for the base case (assign targets, inhale negated condition, run basecase).
      val body_basecase = Seqn(
        assign_targets ++
          Seq(Inhale(Not(ls.cond)())()) ++
          basecase,
        Seq())()

      // Helper to create local var declarations from a list of LocalVars.
      def lv_to_lvd(l : Seq[LocalVar], init : Boolean = false): Seq[LocalVarDecl] = {
        val suffix = if (init) "_init" else ""
        l.map(lv => LocalVarDecl(s"${lv.name}$suffix", lv.typ)())
      }

      // Prepare method parameters: we have `_init` declarations for targets, normal vars for others.
      val targets_init = lv_to_lvd(targets, init = true)
      val args_method = (lv_to_lvd(vars) ++ targets_init)
      val targets_lvd = lv_to_lvd(targets)

      /**
       * Build the inductive-step helper method:
       *   - requires the loop preconditions (with forced `_init` replacements),
       *   - ensures the loop postconditions (also referencing `_init` as needed),
       *   - method body re-checks the loop condition, does body + recursive call if true, or basecase if false.
       */
      val helper_method = Method(
        unique_name_inductive_step,
        args_method,
        targets_lvd,
        Seq(pre_desugar(ls.pres, forceChange = true)),
        Seq(pre_desugar(ls.posts).withMeta(ls.posts.pos, ls.posts.info, ls.posts.errT.+(ErrTrafo({
          case PostconditionViolated(offNode, member, reason, cached) =>
            PostconditionNotPreservedInductiveStep(offNode, reason, cached)
        })))),
        Some(body_inductiveStep)
      )()

      /**
       * Build the base-case helper method:
       *   - requires the same preconditions,
       *   - ensures the same postconditions,
       *   - method body addresses the situation when `cond` is false (no further recursion).
       */
      val helper_method_basecase = Method(
        unique_name_basecase,
        args_method,
        targets_lvd,
        Seq(pre_desugar(ls.pres, forceChange = true)),
        Seq(pre_desugar(ls.posts).withMeta(ls.posts.pos, ls.posts.info, ls.posts.errT.+(ErrTrafo({
          case PostconditionViolated(offNode, member, reason, cached) =>
            PostconditionNotPreservedBaseCase(offNode, reason, cached)
        })))),
        Some(body_basecase)
      )()

      // Replace the loop with a single method call to the inductive-step helper
      // from the original method body.
      val helper_method_call : Seqn =
        Seqn(
          Seq(
            MethodCall(unique_name_inductive_step, args, targets)(NoPosition, NoInfo, ErrTrafo({
              case PreconditionInCallFalse(offNode, reason, cached) =>
                PreconditionNotEstablished(
                  offNode.withMeta(reason.pos, NoInfo, reason.offendingNode.errT),
                  reason,
                  cached
                )
            }))
          ),
          Seq()
        )()

      // Return the call node + the two helper methods to be appended to the program.
      (helper_method_call, helper_method, helper_method_basecase)
    }

    // Collect newly created methods so we can append them at the end.
    var helper_methods : Seq[Method] = Seq()

    // Strategy to rewrite LoopSpecs nodes in the AST with calls to new helper methods.
    val map_loopspecs = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        val (callNode, inductiveM, basecaseM) = mapLoopSpecs(ls)
        helper_methods = helper_methods ++ Seq(inductiveM, basecaseM)
        callNode
    }, Traverse.BottomUp)

    // Apply the rewriting to the original program.
    val curr_program : Program = map_loopspecs.execute(program)

    // Append all helper methods to the program.
    val finalProgram : Program =
      curr_program.copy(methods = curr_program.methods ++ helper_methods)(NoPosition, NoInfo, NoTrafos)

    // Double-check that no leftover PreExp nodes remain outside the intended context.
    finalProgram.transform({
      case p@PreExp(exp) =>
        reportError(ConsistencyError(
          "Found pre expression in an invalid context. " +
            "Only use it in a while loop's postcondition, ghost code, or base case.",
          p.pos
        ))
        exp
    })

    // Perform a final consistency check on the transformed program.
    // It might not type-check or conflict with the outer scope.
    val errs = finalProgram.check
    errs.foreach(reportError)

    finalProgram
  }

  /**
   * Reports an error to the plugin's error mechanism.
   * @param error The AbstractError to report.
   */
  def reportError(error: AbstractError): Unit = {
    loopSpecsPlugin.reportError(error)
  }

}
