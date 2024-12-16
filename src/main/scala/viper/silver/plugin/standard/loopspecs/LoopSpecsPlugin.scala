package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.{LocalVarAssign, _}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{AbstractError, ConsistencyError, Failure, Success, VerificationResult}
import viper.silver.verifier.errors.PreconditionInAppFalse
import fastparse._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.reporter.Entity

import scala.annotation.unused
import scala.collection.immutable.ListMap
import viper.silver.parser.FastParserCompanion.{Pos, reservedKw}



class LoopSpecsPlugin (@unused reporter: viper.silver.reporter.Reporter,
                              @unused logger: ch.qos.logback.classic.Logger,
                              config: viper.silver.frontend.SilFrontendConfig,
                              fp: FastParser)  extends SilverPlugin with ParserPluginTemplate {

  import fp.{predAcc, ParserExtension, lineCol, _file, parenthesizedExp, semiSeparated, precondition, postcondition, stmtBlock, stmt}
  import FastParserCompanion._


  private def deactivated: Boolean = config != null && config.disableTerminationPlugin.toOption.getOrElse(false)

  //TODO: Add some variable in config to choose which version of desugaring: inex, rec




  def ghostBlock[$: P]: P[PGhostBlock] =
    P((reservedKw(PGhostKeyword) ~ ghostBody()) map {case (kw, body) => PGhostBlock(kw, body) _ }).pos

  def ghostBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos


  def baseCaseBlock[$: P]: P[PBaseCaseBlock] =
    P((reservedKw(PBaseCaseKeyword) ~ baseCaseBody()) map { case (kw, body) => PBaseCaseBlock(kw, body) _ }).pos

  def baseCaseBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos



  def loopspecs[$ : P]: P[PLoopSpecs] =

    // Parse the custom while loop
    P(
      (
      reservedKw(PKw.While) ~ parenthesizedExp ~~
      semiSeparated(precondition) ~~
      semiSeparated(postcondition) ~~~
      stmtBlock().lw ~
      ghostBlock.? ~
      baseCaseBlock.?
    ).map {
      case (whileKw, condExp, preSpec, postSpec, bodySeqn, maybeGhost,  maybeBaseCase) =>

        // PGrouped.Paren[PExp]
        PLoopSpecs(
          whileKw,
          condExp,
          preSpec,
          postSpec,
          bodySeqn,
          maybeGhost,
          maybeBaseCase
        )(_)
    }).pos

  def preExpr[$: P]: P[PPreExp] =
    P((reservedKw(PPreKeyword) ~ parenthesizedExp).map{
      case(preKw, exp) =>
        PPreExp(preKw, exp)(_)
    }).pos
  

  /**
   * Add extensions to the parser
   */
  // So that it can parse our new while loop into a PLoopSpecs
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add 3 new keywords: ghost, basecase, pre
    ParserExtension.addNewKeywords(Set(PGhostKeyword, PBaseCaseKeyword, PPreKeyword))
    ParserExtension.addNewExpAtStart(preExpr(_))

    // Add new parser to the precondition
    //ParserExtension.addNewPreCondition(decreases(_))
    // Add new parser to the postcondition
    //ParserExtension.addNewPostCondition(decreases(_))
    // Add new parser to the invariants
    ParserExtension.addNewStmtAtStart(loopspecs(_))
    input
  }

  //Well-definedness
  //TODO: Reject pre(.) if not in post/ghost/bc (manual checking in befVerify()) ==> add test case
  // ALso this is taken care of indircetly by Viper as it will complain about what to do with the pre: don't know how readable
  // the error will be though.
  // ExpectedOutput(consistency.error) as there's no reason
  //TODO: transform final englobing exhale error into post error (override def)


  //TODO: add more examples when this works ==> might lead to more errors.
  override def beforeVerify(input: Program): Program ={
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

      //only copy vardecl outside and assigned inside but not decl inside
      def targets_from_stmts(stmts : Seq[Stmt]): Seq[LocalVar] =
        {
          val decl_inside = stmts.collect({case v : LocalVarDecl => v.name})
          stmts.collect({case v : LocalVarAssign => v.lhs}).filter(lv => !decl_inside.contains(lv.name))
        }

      //TODO: it also cp vars (eg. len) that are targets but don't need a copy as there's never pre(.) anywhere later

      //TODO: add test case: variable scoping, see if finds targets correcctly, declare + assign, don't declare, don't assign...

      //TODO: what about vars decl in basecase and used in body??
      val targets : Seq[LocalVar] =
        targets_from_stmts(ls.body.ss) ++
          targets_from_stmts(ls.basecase.getOrElse(Seqn(Seq(), Seq())()).ss) ++
          targets_from_stmts(ls.ghost.getOrElse(Seqn(Seq(), Seq())()).ss)

      types = types ++ targets.map(_.typ)


      val prefix = "" //"__" //  "__plugin_loopspecs_"

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
        })

      def checkpoint(label : String): Seq[Stmt] =
        Seq(Label(s"$prefix${label}", Seq())()) ++
          copy_targets_with_label(label)


      def call_havoc_type(typ : Type, targets : Seq[LocalVar]): Stmt = {
        MethodCall(
          make_havoc_type(typ).name,
          Seq(),
          targets
        )(NoPosition, NoInfo, NoTrafos)
        //TODO: change this nopos, noinfo??
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
            LocalVar(s"$prefix${label}_${l.name}", l.typ)(l.pos, l.info, l.errT)

          case pre : PreExp => // We only desugared the first pre, further nested pres are simply removed
            pre_desugar_preexp(pre.exp, label)
        })
      }

      def pre_desugar[T <: Node](node : T, label : String): T = {
        node.transform({
          // Even if this was simply a pre around a local var, having a labelled old won't hurt the soundness.
          case pre : PreExp => LabelledOld(pre_desugar_preexp(pre.exp, label), label)(pre.pos, pre.info, pre.errT)
        })
      }

      // Exhale all loop preconditions
      val check_pre: Seq[Stmt] =
        ls.pres.map(pre => Exhale(pre)())

      // Declare a non-deterministic Boolean variable
      val non_det =
        LocalVarDecl(s"${prefix}nondet", Bool)()

      // Common inhalations of preconditions
      val common_to_both_steps: Seq[Stmt] =
        ls.pres.map(pre => Inhale(pre)()) ++
          checkpoint("pre_iteration")

      // Inductive step statements
      val inductive_step: Seq[Stmt] =
        Seq(ls.body) ++
          checkpoint("after_iteration") ++
          ls.pres.map(pre => Exhale(pre)()) ++
          havoc_targets() ++
          ls.posts.map(post => Inhale(pre_desugar(post, "after_iteration"))()) ++
          ls.ghost.map(_.ss).getOrElse(Seq()).map(s => pre_desugar(s, "pre_iteration")) ++
          ls.posts.map(post => Exhale(pre_desugar(post, "pre_iteration"))())

      // Base step statements
      val base_step: Seq[Stmt] =
        ls.basecase.map(_.ss).getOrElse(Seq()).map(s => pre_desugar(s, "pre_iteration")) ++
          ls.posts.map(post => Exhale(pre_desugar(post, "pre_iteration"))())

      // Caller's postconditions
      val callers_post: Seq[Stmt] =
        ls.posts.map(post => Inhale(pre_desugar(post, "pre_loop"))())

      // Construct the transformed sequence
      Seqn(
        checkpoint("pre_loop") ++
          check_pre ++
          havoc_targets() ++
          Seq(
          If(non_det.localVar,
            Seqn(Seq(
              While(TrueLit()(),
                Seq(),
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

    }).execute(input)
    // This is just traversal not verif
    //TODO: test with nested loops (TD /BU)

    // for each type from targets add the havoc methods
    val transformedMethods = newProgram.methods ++ make_havoc_methods()
    newProgram.copy(methods = transformedMethods)(NoPosition, NoInfo, NoTrafos)

  }

  override def reportError(error: AbstractError): Unit = {
    super.reportError(error)
  }
}
