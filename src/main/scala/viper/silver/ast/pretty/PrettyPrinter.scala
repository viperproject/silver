package viper.silver.ast.pretty

import viper.silver.ast._
import scala.collection.immutable.{Queue}
import scala.collection.immutable.Queue.{empty => emptyDq}

/**
 * A pretty printer for the SIL language.
 */
trait FastPrettyPrinterBase {

  import scala.collection.immutable.Seq

  type Indent = Int

  type Width = Int

  /**
    * The final layout of a document as a string.
    */
  type Layout = String

  /**
    * Default indentation is four spaces.
    */
  val defaultIndent = 4

  /**
    * Default layout width is 75 characters.
    */
  val defaultWidth = 75

  /**
    * The operations provided by a pretty-printable document that don't
    * depend on the document's representation type.
    */
  trait DocOps {

    def <> (e : Doc) : Doc

    def <+> (e : Doc) : Doc =
      this <> space <> e

    def <@> (e : Doc) : Doc =
      this <> line <> e

  }

  trait PrettyPrintable {
    def toDoc : Doc = value (this)
  }

  implicit def anyToPrettyPrintable (a : Any) : PrettyPrintable =
    new PrettyPrintable {
      override def toDoc : Doc = value (a)
    }


  def string (s : String) : Doc =
    if (s == "") {
      empty
    } else if (s.charAt(0) == '\n') {
      line <> string (s.tail)
    } else {
      val (xs, ys) = s.span (_ != '\n')
      text (xs) <> string (ys)
    }

  /**
    * Convert a character to a document.  The character can be a newline.
    */
  implicit def char (c : Char) : Doc =
    if (c == '\n')
      line
    else
      text (c.toString)

  def any (a : Any) : Doc =
    if (a == null)
      "null"
    else
      a match {
        case Nil           => "Nil"
        case (l, r)        => any (l) <+> "->" <+> any (r)
        case None          => "None"
        case s : String    => char('\"') <> text (s) <> char('\"')
        case _             => a.toDoc
      }



  def folddoc (ds : Seq[Doc], f : (Doc, Doc) => Doc) =
    if (ds.isEmpty)
      empty
    else
      ds.tail.foldLeft (ds.head) (f)

  def ssep (ds : Seq[Doc], sep : Doc) : Doc =
    folddoc (ds, (_ <> sep <> _))


  def lsep (ds : Seq[Doc], sep : Doc) : Doc =
    if (ds.isEmpty)
      empty
    else
      linebreak <> folddoc (ds, _ <> sep <@> _)


  def value (v : Any) : Doc =
    if (v == null)
      "null"
    else
      string (v.toString)


  def surround (d : Doc, b : Doc) : Doc =
    b <> d <> b


  def braces (d : Doc) : Doc =
    char ('{') <> d <> char ('}')


  def parens (d : Doc) : Doc =
    char ('(') <> d <> char (')')



  def brackets (d : Doc) : Doc =
    char ('[') <> d <> char (']')


  def space : Doc =
    char (' ')




  // Internal data types
  type Remaining = Int
  type Horizontal = Boolean
  type Buffer = String
  type Out = Remaining => Buffer
  type OutGroup = Horizontal => Out => Out
  type PPosition = Int
  type Dq = Queue[(PPosition,OutGroup)]
  type TreeCont = (PPosition,Dq) => Out
  type IW = (Indent,Width)
  type DocCont = IW => TreeCont => TreeCont

  // Helper functions

  private def scan (l : Width, out : OutGroup) (c : TreeCont) : TreeCont =

      (p : PPosition, dq : Dq) =>
        if (dq.isEmpty) {
              val o1 = c (p + l, emptyDq)
              val o2 = out (false) (o1)
             o2
        } else {
          val (s, grp) = dq.last
          val n = (s, (h : Horizontal) =>
            (o1 : Out) =>
                 grp (h) (out (h) (o1))
            )
          prune (c) (p + l, dq.init :+ n)
        }

  private def prune (c1 : TreeCont) : TreeCont =
    (p : PPosition, dq : Dq) =>
        (r : Remaining) =>
          if (dq.isEmpty)
            c1(p,emptyDq) (r)
          else {
            val (s, grp) = dq.head
            if (p > s + r) {
              grp(false) (prune(c1) (p,dq.tail))  (r)
            } else {
              c1 (p, dq) (r)
            }
          }


  private def leave (c : TreeCont) : TreeCont =
    (p : PPosition, dq : Dq) =>
      if (dq.isEmpty) {
        c (p, emptyDq)
      } else if (dq.length == 1) {
        val (s1, grp1) = dq.last
       grp1(true) (c(p,emptyDq))
      } else {
        val (s1, grp1) = dq.last
        val (s2, grp2) = dq.init.last
        val n = (s2, (h : Horizontal) =>
          (o1 : Out) => {
            val o3 =
              (r : Remaining) =>
                    grp1 (p <= s1 + r) (o1) (r)
                 grp2 (h) (o3)
          })
        c (p, dq.init.init :+ n)
      }

  class Doc (f : DocCont) extends DocCont with DocOps {

    def apply (iw : IW) : TreeCont => TreeCont =
      f (iw)

    def <> (e : Doc) : Doc =
      new Doc (
        (iw : IW) =>
          (c1 : TreeCont) =>
                 f (iw) (e (iw) (c1))
      )
  }

  // Basic combinators

   implicit def text (t : String) : Doc =
     if (t == "") empty else
       new Doc (
         (iw : IW) => {
           val l = t.length
           val outText : OutGroup =
             (_ : Horizontal) => (o : Out) =>
               (r : Remaining) =>
                 t + o (r - l)
           scan (l, outText)
         }
       )

  def line (repl : Layout) : Doc =
    new Doc ({
      case (i, w) =>
        val outLine: OutGroup =
          (h : Horizontal) => (c : Out) =>

              (r : Remaining) =>
                if (h)
                   (repl + c (r - repl.length))
                else
                  ("\n" + (" " * i) + c (w - i))
        scan (1, outLine)
    })

  def line : Doc =
    line (" ")

  def linebreak : Doc =
    line ("")

  def empty : Doc =
    new Doc (
      (iw : IW) =>
        (c : TreeCont) =>
          c
    )

  def nest (d : Doc, j : Indent = defaultIndent) : Doc =
    new Doc ({
      case (i, w) =>
        d ((i + j, w))
    })

  // Obtaining output

  def pretty (d : Doc, w : Width = defaultWidth) : Layout = {
    val initBuffer = ("")
    val cend : TreeCont =
      (p : PPosition, dq : Dq) => (r : Remaining) => initBuffer

    val finalBuffer = d(0,w) (cend) (0,emptyDq) (w)
     finalBuffer.toString
  }


}


//stuff needed for the bracket calculation

abstract class Side

trait FastPrettyExpression
case object LeftAssoc extends Side
case object RightAssoc extends Side
case object NonAssoc extends Side

abstract class Fixity
case object Prefix extends Fixity
case object Postfix extends Fixity
case class Infix (side : Side) extends Fixity



trait FastPrettyOperatorExpression  extends FastPrettyExpression {
  def priority : Int
  def fixity : Fixity
}

trait FastPrettyBinaryExpression extends FastPrettyOperatorExpression {
  def left : FastPrettyExpression
  def op : String
  def right : FastPrettyExpression
}
trait FastPrettyUnaryExpression extends FastPrettyOperatorExpression {
  def op : String
  def exp : FastPrettyExpression
}




object FastPrettyPrinter extends  FastPrettyPrinterBase {

  override val defaultIndent = 2

  lazy val uninitialized: Doc = value("<not initialized>")

  /** Pretty-print any AST node. */
  def pretty(n: Node): String = {
    super.pretty(show(n))
  }
  //uses to implement the paper algo, if sees that it has to be bracketed, brackets else not
  def bracket (inner : FastPrettyOperatorExpression, outer : FastPrettyOperatorExpression,
               side : Side) : Doc = {
    val d = toParenDoc (inner)
    if (noparens (inner, outer, side)) d else parens (d)
  }
  //this is part of the algo of the paper, right now it is directly the kiama one
  def noparens (inner : FastPrettyOperatorExpression, outer : FastPrettyOperatorExpression,
                side : Side) : Boolean = {
    val pi = inner.priority
    val po = outer.priority
    lazy val fi = inner.fixity
    lazy val fo = outer.fixity
    (pi < po) ||
      ((fi, side) match {
        case (Postfix, LeftAssoc) =>
          true
        case (Prefix, RightAssoc) =>
          true
        case (Infix (LeftAssoc), LeftAssoc) =>
          (pi == po) && (fo == Infix (LeftAssoc))
        case (Infix (RightAssoc), RightAssoc) =>
          (pi == po) && (fo == Infix (RightAssoc))
        case (_, NonAssoc) =>
          fi == fo
        case _ =>
          false
      })
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
      "{" <+> ssep(exps.to[collection.immutable.Seq] map show, char (',')) <+> "}"
    case null => uninitialized
  }

  /** Show a program. */
  def showProgram(p: Program): Doc = {
    val Program(domains, fields, functions, predicates, methods) = p
    showComment(p) <>
      ssep((domains ++ fields ++ functions ++ predicates ++ methods).to[collection.immutable.Seq] map show, line <> line)
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
        "field" <+> name <> ":" <+> show(typ)
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
                ((if (locals == null) Nil else locals map ("var" <+> showVar(_))) ++
                  Seq(showStmt(body))).to[collection.immutable.Seq], line)
          ) <> line)
      case p@Predicate(name, formalArgs, body) =>
        "predicate" <+> name <> parens(showVars(formalArgs)) <+> (body match {
          case None => empty
          case Some(exp) => braces(nest(line <> show(exp)) <> line)
        })
      case p@Function(name, formalArgs, typ, pres, posts, optBody) =>
        "function" <+> name <> parens(showVars(formalArgs)) <>
          ":" <+> show(typ) <>
          nest(
            showContracts("requires", pres) <>
            showContracts("ensures", posts)
          ) <>
          line <>
          (optBody match {
            case None => empty
            case Some(exp) => braces(nest(line <> show(exp)) <> line)
            case _ => uninitialized
          })
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
      lineIfSomeNonEmpty(contracts) <> ssep((contracts map (name <+> show(_))).to[collection.immutable.Seq], line)
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
  def showVars(vars: Seq[LocalVarDecl]): Doc = ssep((vars map showVar).to[collection.immutable.Seq], char (',') <> space)
  /** Show a variable name with the type of the variable (e.g. to be used in formal argument lists). */
  def showVar(v: LocalVarDecl): Doc = v.name <> ":" <+> showType(v.typ)

  /** Show field name */
  private def showLocation(loc: Location): FastPrettyPrinter.Doc = loc.name

  /** Show a user-defined domain. */
  def showDomain(d: Domain): Doc = {
    d match {
      case Domain(name, functions, axioms, typVars) =>
        "domain" <+> name <>
          (if (typVars.isEmpty) empty else "[" <> ssep((typVars map show).to[collection.immutable.Seq], char (',') <> space) <> "]") <+>
          braces(nest(
            line <> line <>
              ssep(((functions ++ axioms) map show).to[collection.immutable.Seq], line <> line)
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
      case InternalType => "InternalType"
      case Wand => "$WandType"
      case SeqType(elemType) => "Seq" <> "[" <> show(elemType) <> "]"
      case SetType(elemType) => "Set" <> "[" <> show(elemType) <> "]"
      case MultisetType(elemType) => "Multiset" <> "[" <> show(elemType) <> "]"
      case TypeVar(v) => v
      case dt@DomainType(domainName, typVarsMap) =>
        val typArgs = dt.typeParameters map (t => show(typVarsMap.getOrElse(t, t)))
        domainName <> (if (typArgs.isEmpty) empty else brackets(ssep(typArgs.to[collection.immutable.Seq], char (',') <> space)))
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
      case NewStmt(target, fields) =>
        show(target) <+> ":=" <+> "new(" <> ssep((fields map (f => value(f.name))).to[collection.immutable.Seq], char(',') <> space) <>")"
      case LocalVarAssign(lhs, rhs) => show(lhs) <+> ":=" <+> show(rhs)
      case FieldAssign(lhs, rhs) => show(lhs) <+> ":=" <+> show(rhs)
      case Fold(e) => "fold" <+> show(e)
      case Unfold(e) => "unfold" <+> show(e)
      case Package(e) => "package" <+> show(e)
      case Apply(e) => "apply" <+> show(e)
      case Inhale(e) => "inhale" <+> show(e)
      case Exhale(e) => "exhale" <+> show(e)
      case Assert(e) => "assert" <+> show(e)
      case Fresh(vars) =>
        "fresh" <+> ssep((vars map show).to[collection.immutable.Seq], char (',') <> space)
      case Constraining(vars, body) =>
        "constraining" <> parens(ssep((vars map show).to[collection.immutable.Seq], char (',') <> space)) <+> showBlock(body)
      case MethodCall(mname, args, targets) =>
        val call = mname <> parens(ssep((args map show).to[collection.immutable.Seq], char (',') <> space))
        targets match {
          case Nil => call
          case _ => ssep((targets map show).to[collection.immutable.Seq], char (',') <> space) <+> ":=" <+> call
        }
      case Seqn(ss) =>
        val sss = ss filter (s => !(s.isInstanceOf[Seqn] && s.children.isEmpty))
        ssep((sss map show).to[collection.immutable.Seq], line)
      case While(cond, invs, locals, body) =>
        "while" <+> parens(show(cond)) <>
          nest(
            showContracts("invariant", invs)
          ) <+> lineIfSomeNonEmpty(invs) <>
          braces(nest(
            lineIfSomeNonEmpty(locals, body.children) <>
              ssep(
                ((if (locals == null) Nil else locals map ("var" <+> showVar(_))) ++
                  Seq(showStmt(body))).to[collection.immutable.Seq], line)
          ) <> line)
      case If(cond, thn, els) =>
        "if" <+> parens(show(cond)) <+> showBlock(thn) <> showElse(els)
      case Label(name) =>
        "label" <+> name
      case Goto(target) =>
        "goto" <+> target
      case null => uninitialized
    }
    showComment(stmt) <> stmtDoc
  }

  def showElse(els: Stmt): FastPrettyPrinter.Doc = els match {
    case Seqn(Seq()) => empty
    case Seqn(Seq(s)) => showElse(s)
    case If(cond1, thn1, els1) => empty <+> "elseif" <+> parens(show(cond1)) <+> showBlock(thn1) <> showElse(els1)
    case _ => empty <+> "else" <+> showBlock(els)
  }

  /** Outputs the comments attached to `n` if there is at least one. */
  def showComment(n: Infoed): FastPrettyPrinter.Doc = {
    if (n == null)
      empty
    else {
      val comment = n.info.comment
      if (comment.nonEmpty) ssep((comment map ("//" <+> _)).to[collection.immutable.Seq], line) <> line
      else empty
    }
  }

  // Note: pretty-printing expressions is mostly taken care of by kiama
  def toParenDoc(e: FastPrettyExpression): Doc = e match {
    case IntLit(i) => value(i)
    case BoolLit(b) => value(b)
    case NullLit() => value(null)
    case AbstractLocalVar(n) => n
    case FieldAccess(rcv, field) =>
      show(rcv) <> "." <> field.name
    case PredicateAccess(params, predicateName) =>
      predicateName <> parens(ssep((params map show).to[collection.immutable.Seq], char (',') <> space))
    case Unfolding(acc, exp) =>
      parens("unfolding" <+> show(acc) <+> "in" <+> show(exp))
    case UnfoldingGhostOp(acc, exp) =>
      parens("unfolding" <+> show(acc) <+> "in" <+> show(exp))
    case FoldingGhostOp(acc, exp) =>
      parens("folding" <+> show(acc) <+> "in" <+> show(exp))
    case PackagingGhostOp(wand, in) =>
      parens("packaging" <+> show(wand) <+> "in" <+> show(in))
    case ApplyingGhostOp(wand, in) =>
      parens("applying" <+> show(wand) <+> "in" <+> show(in))
    case Old(exp) =>
      "old" <> parens(show(exp))
    case LabelledOld(exp,label) =>
      "old" <> brackets(label) <> parens(show(exp))
    case ApplyOld(exp) =>
      "given" <> parens(show(exp))
    case Let(v, exp, body) =>
      parens("let" <+> show(v) <+> "==" <+> show(exp) <+> "in" <+> show(body))
    case CondExp(cond, thn, els) =>
      parens(show(cond) <+> "?" <+> show(thn) <+> ":" <+> show(els))
    case Exists(v, exp) =>
      parens("exists" <+> showVars(v) <+> "::" <+> show(exp))
    case Forall(v, triggers, exp) =>
      parens("forall" <+> showVars(v) <+> "::" <>
        (if (triggers.isEmpty) empty else space <> ssep((triggers map show).to[collection.immutable.Seq], space)) <+>
        show(exp))
    case ForPerm(v, fields, exp) =>
      parens("forperm"
        <+> brackets(ssep((fields map showLocation).to[collection.immutable.Seq], char (',') <> space))
        <+> v.name <+> "::" <+> show(exp))

    case InhaleExhaleExp(in, ex) =>
      brackets(show(in) <> char (',') <+> show(ex))
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
    case FuncApp(funcname, args) =>
      funcname <> parens(ssep((args map show).to[collection.immutable.Seq], char (',') <> space))
    case DomainFuncApp(funcname, args, _) =>
      funcname <> parens(ssep((args map show).to[collection.immutable.Seq], char (',') <> space))

    case EmptySeq(elemTyp) =>
      "Seq[" <> showType(elemTyp) <> "]()"
    case ExplicitSeq(elems) =>
      "Seq" <> parens(ssep((elems map show).to[collection.immutable.Seq], char (',') <> space))
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
      surround(show(seq),char ('|'))
    case SeqContains(elem, seq) =>
      parens(show(elem) <+> "in" <+> show(seq))

    case EmptySet(elemTyp) =>
      "Set[" <> showType(elemTyp) <> "]()"
    case ExplicitSet(elems) =>
      "Set" <> parens(ssep((elems map show).to[collection.immutable.Seq], char (',') <> space))
    case EmptyMultiset(elemTyp) =>
      "Multiset[" <> showType(elemTyp) <> "]()"
    case ExplicitMultiset(elems) =>
      "Multiset" <> parens(ssep((elems map show).to[collection.immutable.Seq], char (',') <> space))
    case AnySetUnion(left, right) =>
      show(left) <+> "union" <+> show(right)
    case AnySetIntersection(left, right) =>
      show(left) <+> "intersection" <+> show(right)
    case AnySetSubset(left, right) =>
      show(left) <+> "subset" <+> show(right)
    case AnySetMinus(left, right) =>
      show(left) <+> "setminus" <+> show(right)
    case AnySetContains(elem, s) =>
      parens(show(elem) <+> "in" <+> show(s))
    case AnySetCardinality(s) =>
      surround(show(s),char ('|'))

    case null => uninitialized
    case _: FastPrettyUnaryExpression | _: FastPrettyBinaryExpression => {
      e match {
        case b: FastPrettyBinaryExpression =>
          val ld =
            b.left match {
              case l: FastPrettyOperatorExpression =>
                bracket(l, b, LeftAssoc)
              case l =>
                toParenDoc(l)
            }
          val rd =
            b.right match {
              case r: FastPrettyOperatorExpression =>
                bracket(r, b, RightAssoc)
              case r =>
                toParenDoc(r)
            }
          ld <+> text(b.op) <+> rd

        case u: FastPrettyUnaryExpression =>
          val ed =
            u.exp match {
              case e: FastPrettyOperatorExpression =>
                bracket(e, u, NonAssoc)
              case e =>
                toParenDoc(e)
            }
          if (u.fixity == Prefix)
            text(u.op) <> ed
          else
            ed <> text(u.op)

      }
    }
    case _ => sys.error(s"unknown expression: ${e.getClass}")
  }

}
