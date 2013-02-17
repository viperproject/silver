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
    }
  }

  /** Show a program. */
  def showProgram(p: Program): Doc = {
    val Program(name, domains, fields, functions, predicates, methods) = p
    showComment(p) <>
      "program" <+> name <>
      braces(nest(line <>
        lineIfSomeNonEmpty(domains, fields, functions, predicates, domains) <>
          ssep((domains ++ fields ++ functions ++ predicates ++ methods) map show, line <> line)
      ) <> line)
  }

  /** Show a program member. */
  def showMember(m: Member): Doc = {
    val memberDoc = m match {
      case f@Field(name) =>
        "var" <+> name <> ":" <+> show(f.typ)
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
      case p@Predicate(name, body) =>
        "predicate" <+> name <>
          braces(nest(
            line <> show(body)
          ) <> line)
      case p@Function(name, formalArgs, pres, posts, exp) =>
        "function" <+> name <> parens(showVars(formalArgs)) <>
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
  def showVars(vars: Seq[LocalVar]): Doc = ssep(vars map showVar, comma <> space)
  /** Show a variable name with the type of the variable (e.g. to be used in formal argument lists). */
  def showVar(v: LocalVar): Doc = v.name <> ":" <+> showType(v.typ)

  /** Show a user-defined domain. */
  def showDomain(d: Domain): Doc = {
    empty // TODO
  }

  /** Show a type. */
  def showType(typ: Type): Doc = {
    typ match {
      case Bool => "Bool"
      case Int => "Int"
      case Ref => "Ref"
      case Perm => "Perm"
      case Pred => "$PredicateType"
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
      case LocalVarAssign(lhs, rhs) => show(lhs) <+> ":=" <+> show(rhs)
      case FieldAssign(lhs, rhs) => show(lhs) <+> ":=" <+> show(rhs)
      case Fold(e) => "fold" <> parens(show(e))
      case Unfold(e) => "unfold" <> parens(show(e))
      case Inhale(e) => "inhale" <> parens(show(e))
      case Exhale(e) => "exhale" <> parens(show(e))
      case MethodCall(m, rcv, args, targets) =>
        val call = show(rcv) <> "." <> m.name <> parens(ssep(args map show, comma <> space))
        targets match {
          case Nil => call
          case _ => parens(ssep(targets map show, comma <> space)) <+> ":=" <+> call
        }
      case Seqn(ss) =>
        ssep(ss map show, line)
      case While(cond, invs, locals, body) =>
        // TODO: invariants and locals
        "while" <+> "(" <> show(cond) <> ")" <+> showBlock(body)
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
      case AbstractLocalVar(n) => n
      case FieldAccess(rcv, field) =>
        show(rcv) <> "." <> field.name
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
      case FullPerm() =>
        "write"
      case NoPerm() =>
        "0"
      case CurrentPerm(loc) =>
        "perm" <> parens(show(loc))
      case _: PrettyUnaryExpression | _: PrettyBinaryExpression => super.toParenDoc(e)
    }
  }
}
