package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.{Bool, ErrTrafo, Exhale, Exp, If, Inhale, Label, LabelledOld, LocalVar, LocalVarAssign, LocalVarDecl, MakeTrafoPair, Method, MethodCall, NewStmt, NoInfo, NoPosition, NoTrafos, Node, NodeTrafo, Program, Seqn, Stmt, TrueLit, Type, While}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.verifier.{AbstractError, ConsistencyError}
import viper.silver.verifier.errors.ExhaleFailed

/*
TODO: to make plugin into VSCode
1. make jar with silver carbon silicon
 */

class LoopSpecsInhaleExhale(loopSpecsPlugin: LoopSpecsPlugin, val program : Program) {

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


    var types : Set[Type] = Set()

    def make_havoc_methods(): Set[Method] = {
      types.map(t => make_havoc_type(t))
    }
    def make_havoc_type(typ : Type) =
      Method(s"havoc_${typ}",
        Seq(),
        Seq(LocalVarDecl("x", typ)()),
        Seq(),
        Seq(),
        None)()

    def mapLoopSpecs(ls : LoopSpecs): Node = {

    //TODO: test it can get seqn from diff nested scopes
      def targets_from_seqn(seqn: Seqn): Seq[LocalVar] = {
        // All local variable names declared in *this* Seqn (the current scope).
        val declaredInThisScope: Set[String] =
          seqn.scopedDecls.collect { case v: LocalVarDecl => v.name }.toSet

        // All local variables assigned (written) in *this* Seqn (excluding nested Seqn).
        // That means we only look at direct statements in seqn.ss.
        val assignedInThisScope: Seq[LocalVar] = seqn.ss.flatMap {
          case LocalVarAssign(lhs, _) => Some(lhs)
          case NewStmt(lhs, _)        => Some(lhs)
          case MethodCall(_, _, targets) => targets
          case _ => None
        }

        // Recursively collect assigned variables in any nested Seqn statements.
        // We do recursion *after* collecting from this scope,
        // because child scopes may declare new variables that overshadow (or should not leak out).
        val assignedFromSubSeqns: Seq[LocalVar] = seqn.ss.collect {
          case nested: Seqn =>
            // Recursively get targets from the nested scope
            targets_from_seqn(nested)
        }.flatten

        // Combine local assigned variables with the ones from sub-sequences
        val combined = assignedInThisScope ++ assignedFromSubSeqns

        // Filter out the variables that were declared in this very scope.
        // They should *not* bubble up to the parent scope's "undeclared" or external declarations.
        combined.filterNot(lv => declaredInThisScope.contains(lv.name))
      }


      //only copy vardecl outside while loop and assigned inside but not decl inside
      /*def targets_from_stmts(stmts : Seq[Stmt]): Seq[LocalVar] =
      {
        val decl_inside = stmts.flatMap(s => s.collect{case v : LocalVarDecl => v.name})
        stmts.flatMap(_.collect({
          case v : LocalVarAssign => Seq(v.lhs)
          case vt : NewStmt => Seq(vt.lhs)
          case mc : MethodCall => mc.targets
        })).flatten.filter(lv => !decl_inside.contains(lv.name))
      }*/

      // TODO: tsf error as such "  [0] Exhale might fail. There might be insufficient permission to access List(curr) (filter.vpr@47.14--47.24)"
      //  into " Precondition might fail." or the specific part of where it happened.
      //  also: complains on precondition ==> point to actual part of loop (entry start, inductive case, basecase) and same for post(ind, base)

      // added test case: variable scoping, see if finds targets correcctly, declare + assign, don't declare, don't assign...

      //We use distinct to not count twice a var declared oustide and then used in body plus ghost resp.
      /*val targets : Seq[LocalVar] =
        (targets_from_stmts(Seq(ls.body)) ++
          targets_from_stmts(ls.basecase.toSeq) ++
          targets_from_stmts(ls.ghost.toSeq)).distinctBy(lv => lv.name)*/

      val targets: Seq[LocalVar] = ls.writtenVars.intersect(ls.undeclLocalVars)

      /*(
        ls.basecase.map(targets_from_seqn).getOrElse(Seq()) ++
          ls.ghost.map(targets_from_seqn).getOrElse(Seq()) ++
          targets_from_seqn(ls.body)
        ).distinctBy(_.name)*/
      //todo replace with  this if not working anymore

      types = types ++ targets.map(_.typ)


      val prefix = "" //"__" //  "__plugin_loopspecs_"

      //todo add unique name here in an efficient way
      // is unique name deterministic, i think so
      def get_var(label: String, name : String, typ : Type): LocalVar =
        LocalVar(s"$prefix${label}_${name}", typ)()

      def declare_targets_with_label(label : String): Seq[LocalVarDecl] =
        targets.map(t => {
          LocalVarDecl(get_var(label, t.name, t.typ).name, t.typ)()
        })
      //Resolution via name (not ref)
      def copy_targets_with_label(label : String): Seq[Stmt] =
        targets.map(t => {
          LocalVarAssign(get_var(label, t.name, t.typ), t)()
        }) // This can never fail, simple assignment

      def checkpoint(label : String): Seq[Stmt] =
        Seq(Label(s"$prefix${label}", Seq())()) ++
          copy_targets_with_label(label)


      def call_havoc_type(typ : Type, targets : Seq[LocalVar]): Stmt = {
        MethodCall(
          make_havoc_type(typ).name,
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

      //todo: add tests for failures along the way.
      //todo: or if it verifies but shouldn't
      def pre_desugar_preexp(e : Exp, label : String): Exp = {

        e.transform({
          // only rename targets inside pre

          case l: LocalVar if targets.contains(l) =>
            LocalVar(s"$prefix${label}_${l.name}", l.typ)(l.pos, l.info, NodeTrafo(l)) // gets the original vars not the copies

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
        ls.pres.map(pre => Exhale(pre)(pre.pos, pre.info, MakeTrafoPair(pre.errT, ErrTrafo({
          case ExhaleFailed(offNode, reason, cached) =>
            PreconditionNotEstablished(offNode, reason, cached)
        }))))
      }

      // Declare a non-deterministic Boolean variable
      val non_det =
        LocalVarDecl(s"${prefix}nondet", Bool)()

      // Common inhalations of preconditions
      val common_to_both_steps: Seq[Stmt] =
        ls.pres.map(pre => Inhale(pre)()) ++ //TODO: can this fail?
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
          // TODO: try Mix ADT (by default activated) and LS plugins test.
          ls.pres.map(pre => Exhale(pre)(pre.pos, pre.info, MakeTrafoPair(pre.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PreconditionNotPreserved(offNode, reason, cached) // todo: try changing to reason.offNode.pos to get correct conj expr
          })))) ++
          havoc_targets() ++ // always works
          ls.posts.map(post => Inhale(pre_desugar(post, "after_iteration"))()) ++
          ls.ghost.toSeq.map(s => pre_desugar(s, "pre_iteration")) ++
          ls.posts.map(post => Exhale(pre_desugar(post, "pre_iteration"))(post.pos, post.info, MakeTrafoPair(post.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PostconditionNotPreservedInductiveStep(offNode, reason, cached)
          }))))
      // [postcondition.not.preserved.inductive.step:insufficient.permission]

      // Base step statements
      val base_step: Seq[Stmt] =
        ls.basecase.toSeq.map(s => pre_desugar(s, "pre_iteration")) ++
          ls.posts.map(post => Exhale(pre_desugar(post, "pre_iteration"))(post.pos, post.info, MakeTrafoPair(post.errT, ErrTrafo({
            case ExhaleFailed(offNode, reason, cached) =>
              PostconditionNotPreservedBaseCase(offNode, reason, cached)
          }))))

      // Caller's postconditions
      val callers_post: Seq[Stmt] =
        ls.posts.map(post => Inhale(pre_desugar(post, "pre_loop"))())

      // Construct the transformed sequence
      Seqn(
        checkpoint("pre_loop") ++ // always works
          check_pre ++ // exhale failed -> precond not established
          havoc_targets() ++ // always works
          Seq(
            If(non_det.localVar,
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
                Seq())(),
              Seqn(callers_post,
                Seq())()
            )()
          ),
        Seq(non_det) ++ declare_targets_with_label("pre_loop")
      )()
    }
    //inside the seqs of the seqn you have the var decl


    //same as call transform
    val newProgram: Program = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        mapLoopSpecs(ls)

    }).execute(program)
    // This is just traversal not verif
    //TODO: test with nested loops (TD /BU) test


    // Check entire program for pre() that are left
    // There should be no pres. Must be user mistake.

    newProgram.transform({
      case p@PreExp(exp) =>
        reportError(ConsistencyError("Found pre expression in wrong part of program. Please only use it in a while loop's postcondition, ghostcode or base case code.", p.pos));
        exp})


    // for each type from targets add the havoc methods
    val transformedMethods = newProgram.methods ++ make_havoc_methods()
    newProgram.copy(methods = transformedMethods)(NoPosition, NoInfo, NoTrafos)
  }
  def reportError(error: AbstractError): Unit = {
    loopSpecsPlugin.reportError(error)
  }

}
