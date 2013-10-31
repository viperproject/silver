package semper.sil.ast.pretty

import org.kiama.output.{PrettyBinaryExpression, PrettyUnaryExpression, PrettyExpression, ParenPrettyPrinter}
import semper.sil.ast._

/**
 * A pretty printer for the SIL language.
 */
object PrettyPrinter extends org.kiama.output.PrettyPrinter with ParenPrettyPrinter {

  override val defaultIndent = 2

  lazy val uninitialized: Doc = value("<not initialized>")

  /** Pretty-print any AST node. */
  def pretty(n: Node): String = {
    super.pretty(show(n))
  }

  /** Show any AST node. */
  def show(n: Node): Doc = n match {
    case exp: Exp => toParenDoc(exp)
    case stmt: Stmt => showStmt(stmt)
    case typ: Type => showType(typ)
    case p: Program => showProgram(p)
    case m: Member => showMember(m)
    case v: LocalVarDecl => showVar(v)
    case dm: DomainMember => showDomainMember(dm)
    case Trigger(exps) =>
      "{" <+> ssep(exps map show, comma) <+> "}"
    case null => uninitialized
  }

  /** Show a program. */
  def showProgram(p: Program): Doc = {
    val Program(domains, fields, functions, predicates, methods) = p
    showComment(p) <>
      ssep((domains ++ fields ++ functions ++ predicates ++ methods) map show, line <> line)
  }

  /** Show a domain member. */
  def showDomainMember(m: DomainMember): Doc = {
    val memberDoc = m match {
      case f @ DomainFunc(_, _, _, unique) =>
        if (unique) "unique" <+> showDomainFunc(f) else showDomainFunc(f)
      case DomainAxiom(name, exp) =>
        "axiom" <+> name <+>
          braces(nest(
            line <> show(exp)
          ) <> line)
    }
    showComment(m) <> memberDoc
  }


  def showDomainFunc(f: DomainFunc) = {
    val DomainFunc(name, formalArgs, typ, _) = f
    "function" <+> name <> parens(showVars(formalArgs)) <> ":" <+> show(typ)
  }

  /** Show a program member. */
  def showMember(m: Member): Doc = {
    val memberDoc = m match {
      case f@Field(name, typ) =>
        "var" <+> name <> ":" <+> show(typ)
      case m@Method(name, formalArgs, formalReturns, pres, posts, locals, body) =>
        "method" <+> name <> parens(showVars(formalArgs)) <> {
          if (formalReturns.isEmpty) empty
          else empty <+> "returns" <+> parens(showVars(formalReturns))
        } <>
          nest(
            showContracts("requires", pres) <>
            showContracts("ensures", posts)
          ) <>
          line <>
          braces(nest(
            lineIfSomeNonEmpty(locals, if (body == null) null else body.children) <>
              ssep(
                (if (locals == null) Nil else locals map ("var" <+> showVar(_))) ++
                  Seq(showStmt(body)), line)
          ) <> line)
      case p@Predicate(name, formalArgs, body) =>
        "predicate" <+> name <> parens(showVars(formalArgs)) <+>
          braces(nest(
            line <> show(body)
          ) <> line)
      case p@Function(name, formalArgs, typ, pres, posts, exp) =>
        "function" <+> name <> parens(showVars(formalArgs)) <>
          ":" <+> show(typ) <>
          nest(
            showContracts("requires", pres) <>
            showContracts("ensures", posts)
          ) <>
          line <>
          braces(nest(
            line <> show(exp)
          ) <> line)
      case d: Domain =>
        showDomain(d)
    }
    showComment(m) <> memberDoc
  }

  /** Shows contracts and use `name` as the contract name (usually `requires` or `ensures`). */
  def showContracts(name: String, contracts: Seq[Exp]): Doc = {
    if (contracts == null)
      line <> name <+> uninitialized
    else
      lineIfSomeNonEmpty(contracts) <> ssep(contracts map (name <+> show(_)), line)
  }

  /** Returns `n` lines if at least one element of `s` is non-empty, and an empty document otherwise. */
  def lineIfSomeNonEmpty[T](s: Seq[T]*)(implicit n: Int = 1) = {
    if (s.forall(e => e != null && e.isEmpty)) empty
    else {
      var r = empty
      for (i <- 1 to n) r = r <> line
      r
    }
  }

  /** Show a list of formal arguments. */
  def showVars(vars: Seq[LocalVarDecl]): Doc = ssep(vars map showVar, comma <> space)
  /** Show a variable name with the type of the variable (e.g. to be used in formal argument lists). */
  def showVar(v: LocalVarDecl): Doc = v.name <> ":" <+> showType(v.typ)

  /** Show a user-defined domain. */
  def showDomain(d: Domain): Doc = {
    d match {
      case Domain(name, functions, axioms, typVars) =>
        "domain" <+> name <>
          (if (typVars.isEmpty) empty else "[" <> ssep(typVars map show, comma <> space) <> "]") <+>
          braces(nest(
            line <> line <>
              ssep((functions ++ axioms) map show, line <> line)
          ) <> line)
    }
  }

  /** Show a type. */
  def showType(typ: Type): Doc = {
    typ match {
      case Bool => "Bool"
      case Int => "Int"
      case Ref => "Ref"
      case Perm => "Perm"
      case Pred => "$PredicateType"
      case Wand => "$WandType"
      case SeqType(elemType) => "Seq" <> "[" <> show(elemType) <> "]"
      case SetType(elemType) => "Set" <> "[" <> show(elemType) <> "]"
      case MultisetType(elemType) => "Multiset" <> "[" <> show(elemType) <> "]"
      case TypeVar(v) => v
      case DomainType(domain, typVarsMap) =>
        val typArgs = domain.typVars map (t => show(typVarsMap.getOrElse(t, t)))
        domain.name <> (if (typArgs.isEmpty) empty else brackets(ssep(typArgs, comma <> space)))
    }
  }

  /** Show some node inside square braces (with nesting). */
  def showBlock(stmt: Stmt): Doc = {
    braces(nest(
      lineIfSomeNonEmpty(stmt.children) <>
        showStmt(stmt)
    ) <> line)
  }

  /** Show a statement. */
  def showStmt(stmt: Stmt): Doc = {
    val stmtDoc = stmt match {
      case NewStmt(lhs) => show(lhs) <+> ":=" <+> "new()"
      case LocalVarAssign(lhs, rhs) => show(lhs) <+> ":=" <+> show(rhs)
      case FieldAssign(lhs, rhs) => show(lhs) <+> ":=" <+> show(rhs)
      case Fold(e) => "fold" <+> show(e)
      case Unfold(e) => "unfold" <+> show(e)
      case Package(e) => "package" <+> show(e)
      case Apply(e) => "apply" <+> show(e)
      case Inhale(e) => "inhale" <+> show(e)
      case Exhale(e) => "exhale" <+> show(e)
      case Assert(e) => "assert" <+> show(e)
      case FreshReadPerm(vars, body) =>
        "fresh" <> parens(ssep(vars map show, comma <> space)) <+> showBlock(body)
      case MethodCall(m, args, targets) =>
        val call = m.name <> parens(ssep(args map show, comma <> space))
        targets match {
          case Nil => call
          case _ => ssep(targets map show, comma <> space) <+> ":=" <+> call
        }
      case Seqn(ss) =>
        val sss = ss filter (s => !(s.isInstanceOf[Seqn] && s.children.size == 0))
        ssep(sss map show, line)
      case While(cond, invs, locals, body) =>
        // TODO: invariants and locals
        "while" <+> parens(show(cond)) <>
          nest(
            showContracts("invariant", invs)
          ) <+> lineIfSomeNonEmpty(invs) <> showBlock(body)
      case If(cond, thn, els) =>
        "if" <+> parens(show(cond)) <+> showBlock(thn) <> showElse(els)
      case Label(name) =>
        name <> ":"
      case Goto(target) =>
        "goto" <+> target
      case null => uninitialized
    }
    showComment(stmt) <> stmtDoc
  }

  def showElse(els: Stmt): PrettyPrinter.Doc = els match {
    case Seqn(Seq()) => empty
    case Seqn(Seq(s)) => showElse(s)
    case If(cond, thn, els) => empty <+> "elsif" <+> parens(show(cond)) <+> showBlock(thn) <> showElse(els)
    case _ => empty <+> "else" <+> showBlock(els)
  }

  /** Outputs the comments attached to `n` if there is at least one. */
  def showComment(n: Infoed): PrettyPrinter.Doc = {
    if (n == null)
      empty
    else {
      val comment = n.info.comment
      if (comment.size > 0) ssep(comment map ("//" <+> _), line) <> line
      else empty
    }
  }

  // Note: pretty-printing expressions is mostly taken care of by kiama
  override def toParenDoc(e: PrettyExpression): Doc = e match {
    case IntLit(i) => value(i)
    case BoolLit(b) => value(b)
    case NullLit() => value(null)
    case AbstractLocalVar(n) => n
    case FieldAccess(rcv, field) =>
      show(rcv) <> "." <> field.name
    case PredicateAccess(params, predicate) =>
      show(params.head) <> "." <> predicate.name <>
        parens(ssep(params.tail map show, comma <> space))
    case Unfolding(acc, exp) =>
      parens("unfolding" <+> show(acc) <+> "in" <+> show(exp))
    case Folding(acc, exp) =>
      parens("folding" <+> show(acc) <+> "in" <+> show(exp))
    case Applying(wand, in) =>
      parens("applying" <+> show(wand) <+> "in" <+> show(in))
    case Exhaling(exp) =>
      parens("exhaling" <+> show(exp))
    case Old(exp) =>
      "old" <> parens(show(exp))
    case PackageOld(exp) =>
      "pold" <> parens(show(exp))
    case CondExp(cond, thn, els) =>
      parens(show(cond) <+> "?" <+> show(thn) <+> ":" <+> show(els))
    case Exists(v, exp) =>
      parens("exists" <+> showVars(v) <+> "::" <+> show(exp))
    case Forall(v, triggers, exp) =>
      parens("forall" <+> showVars(v) <+> "::" <>
        (if (triggers.isEmpty) empty else space <> ssep(triggers map show, space)) <+>
        show(exp))
    case InhaleExhaleExp(in, ex) =>
      brackets(show(in) <> comma <+> show(ex))
    case WildcardPerm() =>
      "wildcard"
    case FullPerm() =>
      "write"
    case NoPerm() =>
      "none"
    case EpsilonPerm() =>
      "epsilon"
    case CurrentPerm(loc) =>
      "perm" <> parens(show(loc))
    case AccessPredicate(loc, perm) =>
      "acc" <> parens(show(loc) <> "," <+> show(perm))
    case FuncApp(func, args) =>
      func.name <> parens(ssep(args map show, comma <> space))
    case DomainFuncApp(func, args, _) =>
      func.name <> parens(ssep(args map show, comma <> space))

    case EmptySeq(elemTyp) =>
      "Seq()"
    case ExplicitSeq(elems) =>
      "Seq" <> parens(ssep(elems map show, comma <> space))
    case RangeSeq(low, high) =>
      "[" <> show(low) <> ".." <> show(high) <> ")"
    case SeqIndex(seq, idx) =>
      show(seq) <> brackets(show(idx))
    case SeqTake(seq, n) =>
      show(seq) <> brackets(".." <> show(n))
    case SeqDrop(SeqTake(seq, n1), n2) =>
      show(seq) <> brackets(show(n2) <> ".." <> show(n1))
    case SeqDrop(seq, n) =>
      show(seq) <> brackets(show(n) <> "..")
    case SeqUpdate(seq, idx, elem) =>
      show(seq) <> brackets(show(idx) <+> ":=" <+> show(elem))
    case SeqLength(seq) =>
      "|" <> show(seq) <> "|"
    case SeqContains(elem, seq) =>
      show(elem) <+> "in" <+> show(seq)

    case EmptySet(elemTyp) =>
      "Set()"
    case ExplicitSet(elems) =>
      "Set" <> parens(ssep(elems map show, comma <> space))
    case EmptyMultiset(elemTyp) =>
      "Multiset()"
    case ExplicitMultiset(elems) =>
      "Multiset" <> parens(ssep(elems map show, comma <> space))
    case AnySetUnion(left, right) =>
      show(left) <+> "union" <+> show(right)
    case AnySetIntersection(left, right) =>
      show(left) <+> "intersection" <+> show(right)
    case AnySetSubset(left, right) =>
      show(left) <+> "subset" <+> show(right)
    case AnySetMinus(left, right) =>
      show(left) <+> "setminus" <+> show(right)
    case AnySetContains(elem, s) =>
      show(elem) <+> "in" <+> show(s)
    case AnySetCardinality(s) =>
      "|" <> show(s) <> "|"

    case null => uninitialized
    case _: PrettyUnaryExpression | _: PrettyBinaryExpression => super.toParenDoc(e)
    case _ => sys.error(s"unknown expression: ${e.getClass}")
  }

}
