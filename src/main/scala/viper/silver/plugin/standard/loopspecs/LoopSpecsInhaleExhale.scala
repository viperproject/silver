package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.{Bool, ErrTrafo, Exhale, Exp, If, Inhale, Label, LabelledOld, LocalVar, LocalVarAssign, LocalVarDecl, MakeTrafoPair, Method, MethodCall, NewStmt, NoInfo, NoPosition, NoTrafos, Node, NodeTrafo, Program, Seqn, Stmt, TrueLit, Type, While}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.plugin.standard.termination.transformation.ProgramManager
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.verifier.errors.ExhaleFailed

import scala.collection.mutable

/**
 * LoopSpecsInhaleExhale transforms loop specifications into a desugared form using
 * inhale/exhale semantics before program verification.
 *
 * It performs the following tasks:
 *  - Identifies loop components (conditions, preconditions, postconditions, body, ghost, basecase).
 *  - Applies transformations such as variable renaming, havocing, and checkpointing.
 *  - Checks for and reports any errors during the transformation.
 *
 * @param loopSpecsPlugin Plugin for reporting transformation errors.
 * @param program         The Viper program to transform.
 */
class LoopSpecsInhaleExhale(loopSpecsPlugin: LoopSpecsPlugin, val program: Program) extends ProgramManager {

  /**
   * Transforms loop specifications in the program before verification.
   *
   * This method traverses the program, applying a custom transformation to each
   * loop specification (LoopSpecs). It also appends havoc methods for target types
   * and rechecks the final transformed program for any errors.
   *
   * @return The transformed program ready for verification.
   */
  def beforeVerify(): Program = {
    // Mapping from types to their unique havoc method names.
    val havoc_type_to_method_name: mutable.HashMap[Type, String] = mutable.HashMap[Type, String]()

    /**
     * Transforms a LoopSpecs instance into a desugared loop (Seqn).
     *
     * The transformation includes:
     *  - Identifying target variables (intersection of written and undeclared local vars).
     *  - Generating unique names for variables and labels.
     *  - Creating checkpoints and havoc calls.
     *  - Desugaring preconditions and constructing inductive and base steps.
     *
     * @param ls The LoopSpecs to transform.
     * @return   The desugared loop as a Seqn.
     */
    def mapLoopSpecs(ls: LoopSpecs): Seqn = {
      // Identify target variables: those that are both written and undeclared in the augmented while loop's body.
      val targets: Seq[LocalVar] = ls.writtenVars.intersect(ls.undeclLocalVars)

      // Maps for unique names for targets and labels.
      val known_targets: mutable.HashMap[String, String] = mutable.HashMap[String, String]()
      val known_labels: mutable.HashMap[String, String] = mutable.HashMap[String, String]()

      /** Returns a unique label for the given string. */
      def get_label(label: String): String =
        known_labels.getOrElseUpdate(label, uniqueName(label))

      /** Returns a unique name for the given identifier. */
      def get_name(full_name: String): String =
        known_targets.getOrElseUpdate(full_name, uniqueName(full_name))

      /**
       * Returns a unique havoc method name for the given type. If it already exists in the map then it returns the method we will already declare.
       *
       * @param typ       The type for which havoc is needed.
       * @param havocType A string identifier for havoc.
       * @return          A unique havoc method name.
       */
      def get_havoc_name(typ: Type, havocType: String): String =
        havoc_type_to_method_name.getOrElseUpdate(typ, uniqueName(havocType))

      /**
       * Constructs a unique variable name, optionally prefixed with a label.
       *
       * @param label An optional label defining which checkpoint this target copy is for.
       * @param name  The base variable name.
       * @return      A unique variable name = label + _ + name
       */
      def get_var_name(label: String = "", name: String): String = {
        val original_str = s"${if (label != "") get_label(label) else ""}_$name"
        get_name(original_str)
      }

      /**
       * Creates a new LocalVar with a unique name. This way all methods get the same output name through this helper method.
       *
       * @param label An optional label.
       * @param name  The base variable name.
       * @param typ   The type of the variable.
       * @return      A new LocalVar instance.
       */
      def get_var(label: String, name: String, typ: Type): LocalVar = {
        LocalVar(get_var_name(label, name), typ)()
      }

      /**
       * Declares new variables for each target using a given label.
       *
       * @param label The label to use in the variable name.
       * @return      Declaration of all target copies
       */
      def declare_targets_with_label(label: String): Seq[LocalVarDecl] =
        targets.map(t => LocalVarDecl(get_var_name(label, t.name), t.typ)())

      /**
       * Copies target variables by assigning them to their uniquely named counterparts.
       *
       * @param label The label used in the copy.
       * @return      A sequence of assignments of targets to their copies
       */
      def copy_targets_with_label(label: String): Seq[Stmt] =
        targets.map(t => LocalVarAssign(get_var(label, t.name, t.typ), t)()) // Simple assignment.

      /**
       * Creates a checkpoint: a label plus a copy of target variables.
       *
       * @param label The checkpoint label.
       * @return      A label followed by a copy of all targets
       */
      def checkpoint(label: String): Seq[Stmt] =
        Seq(Label(get_label(label), Seq())()) ++ copy_targets_with_label(label)

      /**
       * Creates a havoc method call for a given type and targets.
       *
       * @param typ     The type for havoc.
       * @param targets The target variables.
       * @return        A havoc MethodCall statement.
       */
      def call_havoc_type(typ: Type, targets: Seq[LocalVar]): Stmt = {
        MethodCall(
          get_havoc_name(typ, s"havoc_$typ"),
          Seq(),
          targets
        )(NoPosition, NoInfo, NoTrafos)
      }

      /**
       * Applies havoc operations to all target variables.
       *
       * @return A sequence of havoc statements.
       */
      def havoc_targets(): Seq[Stmt] =
        targets.map(t => call_havoc_type(t.typ, Seq(t)))

      // --- Precondition Desugaring ---

      /**
       * Transforms a pre-expression by renaming target variables inside it.
       *
       * @param e     The expression to transform.
       * @param label The label used for renaming.
       * @return      The transformed expression.
       */
      def pre_desugar_preexp(e: Exp, label: String): Exp = {
        e.transform({
          // Rename target variables within pre expressions.
          case l: LocalVar if targets.contains(l) =>
            LocalVar(get_var_name(label, l.name), l.typ)(l.pos, l.info, NodeTrafo(l))
          // Remove nested pre expressions.
          case pre: PreExp =>
            pre_desugar_preexp(pre.exp, label)
        })
      }

      /**
       * Wraps pre-expressions in a labelled-old construct for soundness.
       *
       * @param node  The node to transform.
       * @param label The label for the transformation.
       * @return      The transformed node.
       */
      def pre_desugar[T <: Node](node: T, label: String): T = {
        node.transform({
          case pre: PreExp =>
            LabelledOld(pre_desugar_preexp(pre.exp, label), label)(pre.pos, pre.info, NodeTrafo(pre))
        })
      }

      // --- End Precondition Desugaring ---

      /**
       * Exhales the loop preconditions, converting any exhale failures to a
       * PreconditionNotEstablished error.
       */
      val check_pre: Seq[Stmt] = {
        Seq(Exhale(ls.pres)(ls.pres.pos, ls.pres.info, MakeTrafoPair(ls.pres.errT, ErrTrafo({
          case ExhaleFailed(offNode, reason, cached) =>
            PreconditionNotEstablished(offNode, reason, cached)
        }))))
      }

      // Declare a non-deterministic Boolean variable for branching.
      val non_det =
        LocalVarDecl(get_var_name(name = "nondet"), Bool)()

      /**
       * Common steps for both inductive and base parts of the loop:
       *  - Inhale the preconditions.
       *  - Establish a checkpoint.
       */
      val common_to_both_steps: Seq[Stmt] =
        Seq(Inhale(ls.pres)()) ++ checkpoint("pre_iteration")

      /**
       * Constructs the inductive step of the loop transformation.
       *
       * This includes:
       *  - The loop body.
       *  - A checkpoint after iteration.
       *  - Exhaling preconditions with transformation of failures.
       *  - Havocing targets.
       *  - Inhaling and exhaling postconditions.
       *  - Applying ghost code if present.
       */
      val inductive_step: Seq[Stmt] =
        Seq(ls.body) ++
          checkpoint("after_iteration") ++
          Seq(Exhale(ls.pres)(ls.pres.pos, ls.pres.info, MakeTrafoPair(ls.pres.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              // TODO: Verify if reason.offNode behaves equivalently.
              PreconditionNotPreserved(offNode, reason, cached)
          })))) ++
          havoc_targets() ++
          Seq(Inhale(pre_desugar(ls.posts, "after_iteration"))()) ++
          ls.ghost.toSeq.map(s => pre_desugar(s, "pre_iteration")) ++
          Seq(Exhale(pre_desugar(ls.posts, "pre_iteration"))(ls.posts.pos, ls.posts.info, MakeTrafoPair(ls.posts.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PostconditionNotPreservedInductiveStep(offNode, reason, cached)
          }))))

      /**
       * Constructs the base step of the loop transformation.
       *
       * This involves desugaring the base case code and exhaling the postconditions.
       */
      val base_step: Seq[Stmt] =
        ls.basecase.toSeq.map(s => pre_desugar(s, "pre_iteration")) ++
          Seq(Exhale(pre_desugar(ls.posts, "pre_iteration"))(ls.posts.pos, ls.posts.info, MakeTrafoPair(ls.posts.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PostconditionNotPreservedBaseCase(offNode, reason, cached)
          }))))

      /**
       * Handles the caller's postconditions after loop termination.
       */
      val callers_post: Seq[Stmt] =
        Seq(Inhale(pre_desugar(ls.posts, "pre_loop"))())

      /**
       * Constructs the "then" branch of the transformed loop. This branch
       * includes the while loop with its inductive and base steps.
       */
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

      /**
       * Constructs the "else" branch containing the caller's postconditions.
       */
      val els: Seqn =
        Seqn(callers_post, Seq())()

      /**
       * Constructs the complete transformed loop as a Seqn.
       *
       * It includes:
       *  - A pre-loop checkpoint.
       *  - Exhaling of preconditions.
       *  - Havoc operations.
       *  - A branching if-statement based on a non-deterministic Boolean.
       */
      val desugared_loop =
        Seqn(
          checkpoint("pre_loop") ++
            check_pre ++
            havoc_targets() ++
            Seq(
              If(non_det.localVar,
                thn,
                els
              )()
            ),
          Seq(non_det) ++ declare_targets_with_label("pre_loop")
        )()
      desugared_loop
    }

    // Apply the transformation to each LoopSpecs element in the program.
    var havoc_methods: Seq[Method] = Seq()
    val newProgram: Program = ViperStrategy.Slim({
      case ls: LoopSpecs =>
        mapLoopSpecs(ls) // Transform the loop specification.
    }).execute(program)
    // This pass is a transformation, not a verification.

    // Ensure no stray pre expressions remain in the program.
    newProgram.transform({
      case p @ PreExp(exp) =>
        reportError(ConsistencyError("Found pre expression in wrong part of program. Please only use it in a while loop's postcondition, ghostcode or base case code.", p.pos))
        exp
    })

    // For each target type, add the corresponding havoc methods.
    havoc_methods = havoc_type_to_method_name.map { f =>
      Method(
        f._2,
        Seq(),
        Seq(LocalVarDecl("x", f._1)()),
        Seq(),
        Seq(),
        None
      )()
    }.toSeq

    // Append havoc methods to the program's method list.
    val transformedMethods = newProgram.methods ++ havoc_methods
    val finalProgram = newProgram.copy(methods = transformedMethods)(NoPosition, NoInfo, NoTrafos)

    // Recheck the transformed program for any errors introduced during transformation.
    // The transformed program might not type-check or could conflict with its outer scope.
    val errs = finalProgram.check
    errs.foreach(reportError(_))
    finalProgram
  }

  /**
   * Reports an error using the LoopSpecsPlugin.
   *
   * @param error The error to report.
   */
  def reportError(error: AbstractError): Unit = {
    loopSpecsPlugin.reportError(error)
  }
}
