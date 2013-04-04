package semper.sil.ast.pretty

import org.kiama.output.{PrettyBinaryExpression, PrettyUnaryExpression, PrettyExpression, ParenPrettyPrinter}
import semper.sil.ast._

/**
 * A pretty printer for the SIL language.
 */
object PrettyPrinter extends org.kiama.output.PrettyPrinter with ParenPrettyPrinter {

  override val defaultIndent = 2

  /** Pretty-print any AST node. */
  def pretty(n: Node): String = {
    super.pretty(show(n))
  }

  /** Show any AST node. */
  def show(n: Node): Doc = {
    n match {
      case exp: Exp => toParenDoc(exp)
      case stmt: Stmt => showStmt(stmt)
      case typ: Type => showType(typ)
      case p: Program => showProgram(p)
      case m: Member => showMember(m)
      case v: LocalVarDecl => showVar(v)
      case dm: DomainMember => showDomainMember(dm)
    }
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
      case DomainFunc(name, formalArgs, typ) =>
        "function" <+> name <> parens(showVars(formalArgs)) <> ":" <+> show(typ)
      case DomainAxiom(name, exp) =>
        "axiom" <+> name <+>
          braces(nest(
            line <> show(exp)
          ) <> line)
    }
    showComment(m) <> memberDoc
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
            lineIfSomeNonEmpty(pres, posts) <>
              ssep(
                (pres map ("requires" <+> show(_))) ++
                  (posts map ("ensures" <+> show(_))), line)
          ) <>
          line <>
          braces(nest(
            lineIfSomeNonEmpty(locals, body.children) <>
              ssep(
                (locals map ("var" <+> showVar(_))) ++
                  Seq(showStmt(body)), line)
          ) <> line)
      case p@Predicate(name, formalArg, body) =>
        "predicate" <+> name <> parens(showVar(formalArg)) <>
          braces(nest(
            line <> show(body)
          ) <> line)
      case p@Function(name, formalArgs, typ, pres, posts, exp) =>
        "function" <+> name <> parens(showVars(formalArgs)) <>
          ":" <+> show(typ) <>
          nest(
            lineIfSomeNonEmpty(pres, posts) <>
              ssep(
                (pres map ("requires" <+> show(_))) ++
                  (posts map ("ensures" <+> show(_))), line)
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

  /** Returns `n` lines if at least one element of `s` is non-empty, and an empty document otherwise. */
  def lineIfSomeNonEmpty[T](s: Seq[T]*)(implicit n: Int = 1) = {
    if (s.forall(_.isEmpty)) empty
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
      case SeqType(elemType) => "Seq" <> "[" <> show(elemType) <> "]"
      case TypeVar(v) => v
      case DomainType(domain, typVarsMap) =>
        val typArgs = domain.typVars map (t => show(typVarsMap.getOrElse(t, t)))
        domain.name <> brackets(ssep(typArgs, comma <> space))
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
      case Inhale(e) => "inhale" <+> show(e)
      case Exhale(e) => "exhale" <+> show(e)
      case Assert(e) => "assert" <+> show(e)
      case FreshReadPerm(vars, body) =>
        "fresh" <> parens(ssep(vars map show, comma <> space)) <+> showBlock(body)
      case MethodCall(m, args, targets) =>
        val call = m.name <> parens(ssep(args map show, comma <> space))
        targets match {
          case Nil => call
          case _ => parens(ssep(targets map show, comma <> space)) <+> ":=" <+> call
        }
      case Seqn(ss) =>
        val sss = ss filter (s => !(s.isInstanceOf[Seqn] && s.children.size == 0))
        ssep(sss map show, line)
      case While(cond, invs, locals, body) =>
        // TODO: invariants and locals
        "while" <+> "(" <> show(cond) <> ")" <>
          nest(
            lineIfSomeNonEmpty(invs) <>
              ssep(invs map ("invariant" <+> show(_)), line)
          ) <+> lineIfSomeNonEmpty(invs) <> showBlock(body)
      case If(cond, thn, els) =>
        "if" <+> "(" <> show(cond) <> ")" <+> showBlock(thn) <> {
          if (els.children.size == 0) empty
          else empty <+> "else" <+> showBlock(els)
        }
      case Label(name) =>
        name <> ":"
      case Goto(target) =>
        "goto" <+> target
    }
    showComment(stmt) <> stmtDoc
  }

  /** Outputs the comments attached to `n` if there is at least one. */
  def showComment(n: Infoed): PrettyPrinter.Doc = {
    val comment = n.info.comment
    if (comment.size > 0) ssep(comment map ("//" <+> _), line) <> line
    else empty
  }

  // Note: pretty-printing expressions is mostly taken care of by kiama
  override def toParenDoc(e: PrettyExpression): Doc = {
    e match {
      case IntLit(i) => value(i)
      case BoolLit(b) => value(b)
      case NullLit() => value(null)
      case AbstractLocalVar(n) => n
      case FieldAccess(rcv, field) =>
        show(rcv) <> "." <> field.name
      case PredicateAccess(rcv, predicate) =>
        show(rcv) <> "." <> predicate.name
      case Unfolding(acc, exp) =>
        parens("unfolding" <+> show(acc) <+> "in" <+> show(exp))
      case Old(exp) =>
        "old" <> parens(show(exp))
      case CondExp(cond, thn, els) =>
        parens(show(cond) <+> "?" <+> show(thn) <+> ":" <+> show(els))
      case Exists(v, exp) =>
        parens("exists" <+> showVar(v) <+> "::" <+> show(exp))
      case Forall(v, exp) =>
        parens("forall" <+> showVar(v) <+> "::" <+> show(exp))
      case ReadPerm() =>
        "read"
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
      case SeqElement(seq, idx) =>
        show(seq) <> brackets(show(idx))
      case SeqTake(seq, n) =>
        show(seq) <> brackets(".." <> show(n))
      case SeqDrop(seq, n) =>
        show(seq) <> brackets(show(n) <> "..")
      case SeqUpdate(seq, idx, elem) =>
        show(seq) <> brackets(show(idx) <+> ":=" <+> show(elem))
      case SeqLength(seq) =>
        "|" <> show(seq) <> "|"
      case _: PrettyUnaryExpression | _: PrettyBinaryExpression => super.toParenDoc(e)
    }
  }
}
