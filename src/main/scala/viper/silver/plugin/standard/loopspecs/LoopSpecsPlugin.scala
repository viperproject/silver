package viper.silver.plugin.standard.loopspecs

import viper.silver.ast.{LocalVarAssign, _}
import viper.silver.ast.utility.ViperStrategy
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser._
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}
import viper.silver.verifier.{ConsistencyError, Failure, Success, VerificationResult}
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


  //private var decreasesClauses: Seq[PDecreasesClause] = Seq.empty

  /**
   * Parser for decreases clauses with following possibilities.
   *
   * decreases (exp (, exp)*)? (if exp)?
   * or
   * decreases _ (if exp)?
   * or
   * decreases *
   */
  /*def decreases[$: P]: P[PSpecification[PDecreasesKeyword.type]] =
    P((P(PDecreasesKeyword) ~ (decreasesWildcard | decreasesStar | decreasesTuple)) map (PSpecification.apply _).tupled).pos
  
  def decreasesTuple[$: P]: P[PDecreasesTuple] =
    P((exp.delimited(PSym.Comma) ~~~ condition.lw.?) map (PDecreasesTuple.apply _).tupled).pos
  def decreasesWildcard[$: P]: P[PDecreasesWildcard] = P((P(PWildcardSym) ~~~ condition.lw.?) map (PDecreasesWildcard.apply _).tupled).pos
  def decreasesStar[$: P]: P[PDecreasesStar] = P(P(PSym.Star) map (PDecreasesStar(_) _)).pos
  def condition[$: P]: P[(PReserved[PIfKeyword.type], PExp)] = 
    P(P(PIfKeyword) ~ exp)
*/

  def ghostBlock[$: P]: P[PGhostBlock] =
    P((reservedKw(PGhostKeyword) ~ ghostBody()) map {case (kw, body) => PGhostBlock(kw, body) _ }).pos

  def ghostBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos


  def baseCaseBlock[$: P]: P[PBaseCaseBlock] =
    P((reservedKw(PBaseCaseKeyword) ~ baseCaseBody()) map { case (kw, body) => PBaseCaseBlock(kw, body) _ }).pos

  def baseCaseBody[$: P](allowDefine: Boolean = true): P[PSeqn] =
    P(semiSeparated(stmt(allowDefine)).braces map PSeqn.apply).pos

  // def old[$: P]: P[PKwOp.Old => Pos => POldExp] = P(oldLabel.brackets.? ~ exp.parens).map {
  //    case (lbl, g) => POldExp(_, lbl, g)
  //  }

  def loopspecs[$ : P]: P[PLoopSpecs] =

    // Parse the custom while loop
    P(
      (
      reservedKw(PKw.While) ~ parenthesizedExp ~~
      semiSeparated(precondition) ~~
      semiSeparated(postcondition) ~
      stmtBlock() ~
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
  
  /*def whileStmt[$: P]: P[PKw.While => Pos => PWhile] =
    P((parenthesizedExp ~~ semiSeparated(invariant) ~ stmtBlock()) 
    map { case (cond, invs, body) => PWhile(_, cond, invs, body) })
    */

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


    //val nonDetLocalVarDecl = LocalVarDecl(s"__plugin_refute_nondet$refutesInMethod", Bool)(r.pos)
    //          Seqn(Seq(
    //            If(nonDetLocalVarDecl.localVar,
    //              Seqn(Seq(
    //                Assert(exp)(r.pos, RefuteInfo(r)),
    //                Inhale(BoolLit(false)(r.pos))(r.pos, Synthesized)
    //              ), Seq())(r.pos),
    //              Seqn(Seq(), Seq())(r.pos))(r.pos)
    //          ),
    //            Seq(nonDetLocalVarDecl)
    //          )(r.pos)

    //1. no assign in ghost ==> error
    //2. or we allow but then treat them

    //copy
    //while()
    //{ ghost{var d:= 0}}
    //
    //only copy vardecl outside and assigned inside but not decl inside

    // some code checks for assignments
    //Todo: Fix this getting types as it currently fails
    var types : Set[Type] = Set(Ref)

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

      def targets_from_stmts(stmts : Seq[Stmt]): Seq[LocalVar] =
        stmts.collect({case v : LocalVarAssign => v.lhs})//.toSeq

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



      def call_havoc_type(typ : Type, targets : Seq[LocalVar]): Stmt =
        MethodCall(
          make_havoc_type(typ).name,
          Seq(),
          targets
        )(NoPosition, NoInfo, NoTrafos)


      def havoc_targets(): Seq[Stmt] =
        targets.map(t  => {
          call_havoc_type(t.typ, Seq(t))
        })

      // s"__plugin_loopspecs_{$name}_{$t.name}" = copy at label name
      // Always put a labelled old -> doesn't hurt
      // pre(list(pre(curr))) == pre(list(curr))
      // pre(accu)
      // post, ghost, basecase
      def pre_desugar_exp(e : Exp, label : String): Exp = {
        e match {
          // Special case: Handle the `PreExp` node
          case pre: PreExp =>
            // Transform its inner exp recursively and wrap in a LabelledOld

            val transformedInner = pre_desugar_exp(pre.exp, label)
            LabelledOld(transformedInner, label)(e.pos, e.info, e.errT)

          // Handle variables
          case l: LocalVar =>
            // Suppose you want to rename variables as "__plugin_loopspecs_<label>_<originalName>"
            LocalVar(s"$prefix${label}_${l.name}", l.typ)(l.pos, l.info, l.errT)

          // Handle binary operations (e.g. Add, Sub, EqCmp, etc.)
          //Todo how to refactor into binop and unop??
          //          case b : BinExp =>
          //            b(pre_transform_vars(b.left), pre_transform_vars(b.right))

          // Handle arithmetic ops
          case Add(l, r) => Add(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Sub(l, r) => Sub(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Mul(l, r) => Mul(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Div(l, r) => Div(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Mod(l, r) => Mod(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)

          // Handle integer comparisons
          case LtCmp(l, r) => LtCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case LeCmp(l, r) => LeCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case GtCmp(l, r) => GtCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case GeCmp(l, r) => GeCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)

          // Handle equality
          case EqCmp(l, r) => EqCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case NeCmp(l, r) => NeCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)

          // Handle boolean ops
          case And(l, r) => And(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Or(l, r) => Or(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Implies(l, r) => Implies(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case Not(exp) => Not(pre_desugar_exp(exp, label))(e.pos, e.info, e.errT)

          // Handle MagicWand
          case MagicWand(l, r) =>
            MagicWand(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)

          // Handle Old, LabelledOld
          case Old(exp) => Old(pre_desugar_exp(exp, label))(e.pos, e.info, e.errT)
          case LabelledOld(exp, oldLabel) =>
            LabelledOld(pre_desugar_exp(exp, label), oldLabel)(e.pos, e.info, e.errT)

          // Handle Literals
          case i: IntLit => i
          case TrueLit() => TrueLit()(e.pos, e.info, e.errT)
          case FalseLit() => FalseLit()(e.pos, e.info, e.errT)
          case NullLit() => NullLit()(e.pos, e.info, e.errT)

          // Handle Minus (unary negation)
          case Minus(exp) => Minus(pre_desugar_exp(exp, label))(e.pos, e.info, e.errT)

          // Handle Permissions
          case FullPerm() => FullPerm()(e.pos, e.info, e.errT)
          case NoPerm() => NoPerm()(e.pos, e.info, e.errT)
          case EpsilonPerm() => EpsilonPerm()(e.pos, e.info, e.errT)
          case FractionalPerm(l, r) =>
            FractionalPerm(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermDiv(l, r) =>
            PermDiv(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermPermDiv(l, r) =>
            PermPermDiv(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case CurrentPerm(res) =>
            CurrentPerm(res match {
              case FieldAccess(rcv, fld) =>
                FieldAccess(pre_desugar_exp(rcv, label), fld)(res.pos, res.info, res.errT)
              case PredicateAccess(args, pname) =>
                PredicateAccess(args.map(a => pre_desugar_exp(a, label)), pname)(res.pos, res.info, res.errT)
              // If more ResourceAccess types exist, handle them here
            })(e.pos, e.info, e.errT)

          // Handle Permission arithmetic
          case PermMinus(exp) =>
            PermMinus(pre_desugar_exp(exp, label))(e.pos, e.info, e.errT)
          case PermAdd(l, r) =>
            PermAdd(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermSub(l, r) =>
            PermSub(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermMul(l, r) =>
            PermMul(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case IntPermMul(l, r) =>
            IntPermMul(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermLtCmp(l, r) =>
            PermLtCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermLeCmp(l, r) =>
            PermLeCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermGtCmp(l, r) =>
            PermGtCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case PermGeCmp(l, r) =>
            PermGeCmp(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case DebugPermMin(l, r) =>
            DebugPermMin(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)

          // Handle FuncApp and DomainFuncApp
          case FuncApp(fname, args) =>
            FuncApp(fname, args.map(a => pre_desugar_exp(a, label)))(e.pos, e.info, e.typ, e.errT)
          case d@DomainFuncApp(fname, args, tvm) =>
            DomainFuncApp(fname, args.map(a => pre_desugar_exp(a, label)), tvm)(d.pos, d.info, d.typ, d.domainName, d.errT)
          case BackendFuncApp(bfname, args) =>
            BackendFuncApp(bfname, args.map(a => pre_desugar_exp(a, label)))(e.pos, e.info, e.typ, e.asInstanceOf[BackendFuncApp].interpretation, e.errT)

          // Handle Access predicates
          case FieldAccess(rcv, fld) =>
            FieldAccess(pre_desugar_exp(rcv, label), fld)(e.pos, e.info, e.errT)
          case PredicateAccess(args, pname) =>
            PredicateAccess(args.map(a => pre_desugar_exp(a, label)), pname)(e.pos, e.info, e.errT)

          case PredicateAccessPredicate(loc, perm) =>
            PredicateAccessPredicate(
              PredicateAccess(loc.args.map(a => pre_desugar_exp(a, label)), loc.predicateName)(),
              perm
            )(e.pos, e.info, e.errT)

          case FieldAccessPredicate(loc, perm) =>
            FieldAccessPredicate(
              FieldAccess(pre_desugar_exp(loc.rcv, label), loc.field)(),
              perm
            )(e.pos, e.info, e.errT)

          // Handle CondExp
          case CondExp(c, t, f) =>
            CondExp(pre_desugar_exp(c, label), pre_desugar_exp(t, label), pre_desugar_exp(f, label))(e.pos, e.info, e.errT)

          // Handle Unfolding, Applying, Asserting
          case Unfolding(acc, body) =>
            val newAcc = PredicateAccessPredicate(
              PredicateAccess(acc.loc.args.map(a => pre_desugar_exp(a, label)), acc.loc.predicateName)(acc.loc.pos, acc.loc.info, acc.loc.errT),
              pre_desugar_exp(acc.perm, label)
            )(acc.pos, acc.info, acc.errT)
            Unfolding(newAcc, pre_desugar_exp(body, label))(e.pos, e.info, e.errT)
          case Applying(wand, body) =>
            Applying(
              MagicWand(pre_desugar_exp(wand.left, label), pre_desugar_exp(wand.right, label))(wand.pos, wand.info, wand.errT),
              pre_desugar_exp(body, label)
            )(e.pos, e.info, e.errT)
          case Asserting(a, body) =>
            Asserting(pre_desugar_exp(a, label), pre_desugar_exp(body, label))(e.pos, e.info, e.errT)

          // Handle Let
          case Let(vd, exp, body) =>
            Let(
              LocalVarDecl(vd.name, vd.typ)(vd.pos, vd.info, vd.errT), // If you need to rename let-bound vars, do so here
              pre_desugar_exp(exp, label),
              pre_desugar_exp(body, label)
            )(e.pos, e.info, e.errT)

          // Handle Quantified expressions
          case Forall(vars, triggers, exp) =>
            // Typically you do NOT rename quantified variables here, as that changes semantics.
            // Just transform the body if needed.
            Forall(vars, triggers, pre_desugar_exp(exp, label))(e.pos, e.info, e.errT)
          case Exists(vars, triggers, exp) =>
            Exists(vars, triggers, pre_desugar_exp(exp, label))(e.pos, e.info, e.errT)
          case ForPerm(vars, resource, body) =>
            // Similar approach, transform resource and body
            val newRes = resource match {
              case FieldAccess(rcv, fld) =>
                FieldAccess(pre_desugar_exp(rcv, label), fld)(resource.pos, resource.info, resource.errT)
              case PredicateAccess(args, pname) =>
                PredicateAccess(args.map(a => pre_desugar_exp(a, label)), pname)(resource.pos, resource.info, resource.errT)
              case _ => resource // in case of unexpected resource type
            }
            ForPerm(vars, newRes, pre_desugar_exp(body, label))(e.pos, e.info, e.errT)

          // Handle sequence expressions
          case EmptySeq(et) => EmptySeq(et)(e.pos, e.info, e.errT)
          case ExplicitSeq(elems) =>
            ExplicitSeq(elems.map(a => pre_desugar_exp(a, label)))(e.pos, e.info, e.errT)
          case RangeSeq(low, high) =>
            RangeSeq(pre_desugar_exp(low, label), pre_desugar_exp(high, label))(e.pos, e.info, e.errT)
          case SeqAppend(l, r) =>
            SeqAppend(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case SeqIndex(s, idx) =>
            SeqIndex(pre_desugar_exp(s, label), pre_desugar_exp(idx, label))(e.pos, e.info, e.errT)
          case SeqTake(s, n) =>
            SeqTake(pre_desugar_exp(s, label), pre_desugar_exp(n, label))(e.pos, e.info, e.errT)
          case SeqDrop(s, n) =>
            SeqDrop(pre_desugar_exp(s, label), pre_desugar_exp(n, label))(e.pos, e.info, e.errT)
          case SeqContains(elem, s) =>
            SeqContains(pre_desugar_exp(elem, label), pre_desugar_exp(s, label))(e.pos, e.info, e.errT)
          case SeqUpdate(s, idx, elem) =>
            SeqUpdate(pre_desugar_exp(s, label), pre_desugar_exp(idx, label), pre_desugar_exp(elem, label))(e.pos, e.info, e.errT)
          case SeqLength(s) =>
            SeqLength(pre_desugar_exp(s, label))(e.pos, e.info, e.errT)

          // Handle sets and multisets
          case EmptySet(et) => EmptySet(et)(e.pos, e.info, e.errT)
          case ExplicitSet(elems) =>
            ExplicitSet(elems.map(a => pre_desugar_exp(a, label)))(e.pos, e.info, e.errT)
          case EmptyMultiset(et) => EmptyMultiset(et)(e.pos, e.info, e.errT)
          case ExplicitMultiset(elems) =>
            ExplicitMultiset(elems.map(a => pre_desugar_exp(a, label)))(e.pos, e.info, e.errT)

          case AnySetUnion(l, r) =>
            AnySetUnion(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case AnySetIntersection(l, r) =>
            AnySetIntersection(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case AnySetSubset(l, r) =>
            AnySetSubset(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case AnySetMinus(l, r) =>
            AnySetMinus(pre_desugar_exp(l, label), pre_desugar_exp(r, label))(e.pos, e.info, e.errT)
          case AnySetContains(elem, s) =>
            AnySetContains(pre_desugar_exp(elem, label), pre_desugar_exp(s, label))(e.pos, e.info, e.errT)
          case AnySetCardinality(s) =>
            AnySetCardinality(pre_desugar_exp(s, label))(e.pos, e.info, e.errT)

          // Handle maps
          case EmptyMap(k, v) => EmptyMap(k, v)(e.pos, e.info, e.errT)
          case ExplicitMap(elems) =>
            ExplicitMap(elems.map(a => pre_desugar_exp(a, label)))(e.pos, e.info, e.errT)
          case Maplet(key, value) =>
            Maplet(pre_desugar_exp(key, label), pre_desugar_exp(value, label))(e.pos, e.info, e.errT)
          case MapUpdate(base, key, value) =>
            MapUpdate(
              pre_desugar_exp(base, label),
              pre_desugar_exp(key, label),
              pre_desugar_exp(value, label)
            )(e.pos, e.info, e.errT)
          case MapLookup(base, key) =>
            MapLookup(
              pre_desugar_exp(base, label),
              pre_desugar_exp(key, label)
            )(e.pos, e.info, e.errT)
          case MapContains(key, base) =>
            MapContains(pre_desugar_exp(key, label), pre_desugar_exp(base, label))(e.pos, e.info, e.errT)
          case MapCardinality(base) =>
            MapCardinality(pre_desugar_exp(base, label))(e.pos, e.info, e.errT)
          case MapDomain(base) =>
            MapDomain(pre_desugar_exp(base, label))(e.pos, e.info, e.errT)
          case MapRange(base) =>
            MapRange(pre_desugar_exp(base, label))(e.pos, e.info, e.errT)

          // If you have any ExtensionExp
          case ext: ExtensionExp =>
            // If needed, transform extensionSubnodes:
            val newSubnodes = ext.extensionSubnodes.map {
              case ee: Exp => pre_desugar_exp(ee, label)
              case n => n
            }
            new ExtensionExp() {
              override def extensionIsPure: Boolean = ext.extensionIsPure

              override def extensionSubnodes: Seq[Node] = newSubnodes

              override def typ: Type = ext.typ

              override def verifyExtExp(): VerificationResult = ext.verifyExtExp()

              /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
               * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
              override def prettyPrint: PrettyPrintPrimitives#Cont = ext.prettyPrint

              override def canEqual(that: Any): Boolean = ext.canEqual(that)

              override def info: Info = ext.info

              override def pos: Position = ext.pos

              override def errT: ErrorTrafo = ext.errT

              override def productArity : Int = ext.productArity
              override def productElement(n: Int): Any = ext.productElement(n)

            }


          // Catch-all: If a new expression type is added and not handled:
          case other =>
            sys.error(s"Unhandled expression type: ${other.getClass}")
        }
      }

      def pre_desugar_stmt(s: Stmt, label: String): Stmt = s match {
        // Simple statements that contain expressions
        case NewStmt(lhs, fields) =>
          // NewStmt has no Exp to transform, lhs is a LocalVar (Exp) but likely doesn't need "pre" treatment.
          // If necessary, transform lhs using pre_desugar_exp(lhs,label) if you treat LocalVars as Exps
          // Fields are just Fields, no Exp inside.
          s

        case LocalVarAssign(lhs, rhs) =>
          LocalVarAssign(lhs, pre_desugar_exp(rhs, label))(s.pos, s.info, s.errT)

        case FieldAssign(lhs, rhs) =>
          FieldAssign(lhs, pre_desugar_exp(rhs, label))(s.pos, s.info, s.errT)

        case MethodCall(m, args, targets) =>
          MethodCall(m, args.map(a => pre_desugar_exp(a, label)), targets)(s.pos, s.info, s.errT)

        case Exhale(exp) =>
          Exhale(pre_desugar_exp(exp, label))(s.pos, s.info, s.errT)

        case Inhale(exp) =>
          Inhale(pre_desugar_exp(exp, label))(s.pos, s.info, s.errT)

        case Assert(exp) =>
          Assert(pre_desugar_exp(exp, label))(s.pos, s.info, s.errT)

        case Assume(exp) =>
          Assume(pre_desugar_exp(exp, label))(s.pos, s.info, s.errT)

        case Fold(acc) =>
          // acc is a PredicateAccessPredicate, which contains `perm` and `loc` fields that can contain Exps.
          val transformedAcc = PredicateAccessPredicate(
            PredicateAccess(acc.loc.args.map(a => pre_desugar_exp(a, label)), acc.loc.predicateName)(),
            acc.perm
          )(acc.pos, acc.loc.info, acc.loc.errT)
          Fold(transformedAcc)(
            acc.pos, acc.info, acc.errT)

        case Unfold(acc) =>
          // Similar to Fold
          val transformedAcc = PredicateAccessPredicate(
            PredicateAccess(acc.loc.args.map(a => pre_desugar_exp(a, label)), acc.loc.predicateName)(),
            acc.perm
          )(acc.pos, acc.loc.info, acc.loc.errT)
          Unfold(transformedAcc)(
            acc.pos, acc.info, acc.errT)

        case Package(wand, proofScript) =>
          val transformedWand = MagicWand(
            pre_desugar_exp(wand.left, label),
            pre_desugar_exp(wand.right, label)
          )(wand.pos, wand.info, wand.errT)
          Package(transformedWand, pre_desugar_stmt(proofScript, label).asInstanceOf[Seqn])(s.pos, s.info, s.errT)

        case Apply(exp) =>
          val transformedWand = MagicWand(
            pre_desugar_exp(exp.left, label),
            pre_desugar_exp(exp.right, label)
          )(exp.pos, exp.info, exp.errT)
          Apply(transformedWand)(s.pos, s.info, s.errT)

        case Seqn(ss, decls) =>
          Seqn(ss.map(stmt => pre_desugar_stmt(stmt, label)), decls)(s.pos, s.info, s.errT)

        case If(cond, thn, els) =>
          If(
            pre_desugar_exp(cond, label),
            pre_desugar_stmt(thn, label).asInstanceOf[Seqn],
            pre_desugar_stmt(els, label).asInstanceOf[Seqn]
          )(s.pos, s.info, s.errT)

        case While(cond, invs, body) =>
          While(
            pre_desugar_exp(cond, label),
            invs.map(i => pre_desugar_exp(i, label)),
            pre_desugar_stmt(body, label).asInstanceOf[Seqn]
          )(s.pos, s.info, s.errT)

        case Label(name, invs) =>
          Label(
            name,
            invs.map(i => pre_desugar_exp(i, label))
          )(s.pos, s.info, s.errT)

        case Goto(target) =>
          s // no expressions here

        case LocalVarDeclStmt(decl) =>
          s // no expressions to transform

        case Quasihavoc(lhs, exp) =>
          Quasihavoc(
            lhs.map(e => pre_desugar_exp(e, label)),
            exp match {
              case fa: FieldAccess =>
                FieldAccess(pre_desugar_exp(fa.rcv, label), fa.field)(fa.pos, fa.info, fa.errT)
              case pa: PredicateAccess =>
                PredicateAccess(pa.args.map(a => pre_desugar_exp(a, label)), pa.predicateName)(pa.pos, pa.info, pa.errT)
            }
          )(s.pos, s.info, s.errT)

        case Quasihavocall(vars, lhs, exp) =>
          Quasihavocall(
            vars,
            lhs.map(e => pre_desugar_exp(e, label)),
            exp match {
              case fa: FieldAccess =>
                FieldAccess(pre_desugar_exp(fa.rcv, label), fa.field)(fa.pos, fa.info, fa.errT)
              case pa: PredicateAccess =>
                PredicateAccess(pa.args.map(a => pre_desugar_exp(a, label)), pa.predicateName)(pa.pos, pa.info, pa.errT)
            }
          )(s.pos, s.info, s.errT)

          //todo: should i implement support for this??
        case ext: ExtensionStmt =>
          // Transform expressions inside extensionSubnodes if needed:
          // This depends on what extension nodes contain.
          // Example pseudo-code:
          // val transformedNodes = ext.extensionSubnodes.map(transformNodeIfExp)
          // ext.copyWithNewSubnodes(transformedNodes)
          ext

        case other =>
          sys.error(s"Unhandled stmt type: ${other.getClass}")
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
          ls.posts.map(post => Inhale(pre_desugar_exp(post, "after_iteration"))()) ++
          ls.ghost.map(_.ss).getOrElse(Seq()).map(s => pre_desugar_stmt(s, "pre_iteration")) ++
          ls.posts.map(post => Exhale(pre_desugar_exp(post, "pre_iteration"))())

      // Base step statements
      val base_step: Seq[Stmt] =
        ls.basecase.map(_.ss).getOrElse(Seq()).map(s => pre_desugar_stmt(s, "pre_iteration")) ++
          ls.posts.map(post => Exhale(pre_desugar_exp(post, "pre_iteration"))())

      // Caller's postconditions
      val callers_post: Seq[Stmt] =
        ls.posts.map(post => Inhale(pre_desugar_exp(post, "pre_loop"))())



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



    val newProgram: Program = ViperStrategy.Slim({
      case ls : LoopSpecs =>
        mapLoopSpecs(ls)

      case p: Program =>
        // for each type from targets add the havoc methods

        val transformedMethods = p.methods ++ make_havoc_methods()

        Program(p.domains, p.fields, p.functions, p.predicates, transformedMethods, p.extensions)(p.pos, p.info, p.errT)
        //ext is for toplevel decl
    }, Traverse.TopDown).execute(input) //TODO: TD or BU ??
    newProgram



  }
}
