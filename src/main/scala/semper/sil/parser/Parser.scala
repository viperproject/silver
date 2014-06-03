package semper.sil.parser

import java.nio.file.Path
import org.kiama.util.WhitespacePositionedParserUtilities

/**
 * A parser for the SIL language that takes a string and produces an intermediate
 * AST ([[semper.sil.parser.PNode]]), or a parse error.  The intermediate AST can
 * then be type-checked and translated into the SIL AST ([[semper.sil.ast.Node]])
 * using [[semper.sil.parser.Translator]].
 *
 * IMPORTANT: If you change or extend the syntax, please also update the synatx
 * description in documentation/syntax as well as the syntax highlighting definitions
 * in util/highlighting!
 *
 * IMPORTANT: Also keep the parser in sync with the pretty printer!
 */
object Parser extends BaseParser {
  override def file = _file
  var _file: Path = null

  def parse(s: String, f: Path) = {
    _file = f
    val r = parseAll(parser, s)
    r match {
      // make sure the tree is correctly initialized
      case Success(e, _) => e.initTreeProperties()
      case _ =>
    }
    r
  }
}


/* A parser intended for debugging. Extend it and make parsing rules log their invocation
 * by changing a rule such as
 *   lazy val foo = body
 * to
 *   lazy val foo = "foo" !!! body
 *
 * Taken from http://jim-mcbeath.blogspot.be/2011/07/debugging-scala-parser-combinators.html
 */

import scala.language.implicitConversions
import scala.language.reflectiveCalls

object DebuggingParser {
  var depth: Int = 0
}

trait DebuggingParser extends WhitespacePositionedParserUtilities {
  class Wrap[+T](name:String, parser: Parser[T]) extends PackratParser[T] {
    def apply(in: Input): ParseResult[T] = {
      val indent = " " * DebuggingParser.depth
      DebuggingParser.depth += 1

      println(s"$indent<$name> for '${in.first}' at ${in.pos}")
      val t = parser.apply(in)
      val fr = if (t.successful) " for " + t.get else ""
      println(s"$indent</$name> ${t.getClass.getSimpleName} at ${t.next.pos}$fr")

      DebuggingParser.depth - 1

      t
    }
  }

  implicit def toWrapped(name: String) = new {
    def !!![T](p: Parser[T]) = new Wrap(name,p)
  }
}


/* This parser is a PackratParser and thus CAN support left recursive parsing
 * rules with memoisation. You have to EXPLICITLY declare the return type of
 * such rules as PackratPerser[T], though. Moreover, if sub-rules further down
 * the line are not declared to return a PackratParser, then the memoisation
 * won't be total and the run-time is no longer linear. Mixing different
 * parsers is otherwise fine.
 *
 * See the Kiama documentation for further information, for example,
 * http://code.google.com/p/kiama/wiki/ParserCombs.
 */
trait BaseParser extends /*DebuggingParser*/ WhitespacePositionedParserUtilities {

  /** The file we are currently parsing (for creating positions later). */
  def file: Path

  /**
   * All keywords of SIL.
   *
   * IMPORTANT: If you add any new keywords, please also update all syntax highlighters
   * in util/highlighting.  Also update the SIL syntax description in documentation/syntax.
   */
  val reserved = List(
    // special variables
    "result",
    // types
    "Int", "Perm", "Bool", "Ref",
    // boolean constants
    "true", "false",
    // null
    "null",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom", "var", "returns", "field", "define", "wand",
    // specifications
    "requires", "ensures", "invariant",
    // statements
    "fold", "unfold", "inhale", "exhale", "new", "assert", "assume", "goto", "package", "apply",
    // control structures
    "while", "if", "elsif", "else",
    // special fresh block
    "fresh", "constraining",
    // sequences
    "Seq",
    // sets and multisets
    "Set", "Multiset", "union", "intersection", "setminus", "subset",
    // prover hint expressions
    "unfolding", "in", "folding", "applying",
    // old expression
    "old", "now", "lhs",
    // quantification
    "forall", "exists",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique",

    // TODO: Hacks to stop the parser from interpreting, e.g., "inhale" as "in hale"
    "variant", "hale", "tersection"
  )

  lazy val parser = phrase(programDecl)

  // --- Whitespace

  lazy val whitespaceParser: PackratParser[Any] =
    rep(whiteSpace | comment)

  lazy val comment: PackratParser[Any] =
    ("/*" ~ rep(not("*/") ~ (comment | any)) ~ "*/") |
      ("//" ~ rep(not("\n") ~ any))

  // --- Declarations

  lazy val programDecl =
    rep(domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl) ^^ {
      case decls =>
        val domains = decls collect {
          case d: PDomain => d
        }
        val fields = decls collect {
          case d: PField => d
        }
        val functions = decls collect {
          case d: PFunction => d
        }
        val predicates = decls collect {
          case d: PPredicate => d
        }
        val methods = decls collect {
          case d: PMethod => d
        }
        PProgram(file, domains, fields, functions, predicates, methods)
    }

  lazy val fieldDecl =
    ("field" ~> idndef) ~ (":" ~> typ <~ opt(";")) ^^ PField

  lazy val methodDecl =
    methodSignature ~ rep(pre) ~ rep(post) ~ block ^^ {
      case name ~ args ~ rets ~ pres ~ posts ~ body =>
        PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(body))
    }

  lazy val methodSignature =
    ("method" ~> idndef) ~ ("(" ~> formalArgList <~ ")") ~ opt("returns" ~> ("(" ~> formalArgList <~ ")"))
  lazy val pre =
    "requires" ~> exp <~ opt(";")
  lazy val post =
    "ensures" ~> exp <~ opt(";")
  lazy val inv =
    "invariant" ~> exp <~ opt(";")

  lazy val formalArgList =
    repsep(formalArg, ",")
  lazy val formalArg =
    idndef ~ (":" ~> typ) ^^ PFormalArgDecl

  lazy val functionDecl =
    functionSignature ~ rep(pre) ~ rep(post) ~ ("{" ~> (exp <~ "}")) ^^ PFunction
  lazy val functionSignature =
    ("function" ~> idndef) ~ ("(" ~> formalArgList <~ ")") ~ (":" ~> typ)

  lazy val domainFunctionDecl = opt("unique") ~ (functionSignature <~ opt(";")) ^^ {
    case unique ~ fdecl =>
      fdecl match {
        case name ~ formalArgs ~ t => PDomainFunction(name, formalArgs, t, unique.isDefined)
      }
  }

  lazy val predicateDecl =
    ("predicate" ~> idndef) ~ ("(" ~> formalArgList <~ ")") ~ ("{" ~> (exp <~ "}")) ^^ PPredicate

  lazy val domainDecl =
    ("domain" ~> idndef) ~
      opt("[" ~> repsep(idndef, ",") <~ "]") ~
      ("{" ~> rep(domainFunctionDecl)) ~
      (rep(axiomDecl) <~ "}") ^^ {
      case name ~ typparams ~ funcs ~ axioms =>
        PDomain(name, typparams.getOrElse(Nil), funcs, axioms)
    }

  lazy val axiomDecl =
    ("axiom" ~> idndef) ~ ("{" ~> (exp <~ "}")) <~ opt(";") ^^ PAxiom

  // --- Statements

  def parens[A](p: Parser[A]) = "(" ~> p <~ ")"

  lazy val block: Parser[Seq[PStmt]] =
    "{" ~> (stmts <~ "}")
  lazy val stmts =
    rep(stmt <~ opt(";"))
  lazy val stmt =
    fieldassign | localassign | fold | unfold | exhale | assert |
      inhale | ifthnels | whle | varDecl | letassDecl | letwandDecl | newstmt | fresh | constrainingBlock |
      methodCall | goto | lbl | packageWand | applyWand

  lazy val fold =
    "fold" ~> predicateAccessPred ^^ PFold
  lazy val unfold =
    "unfold" ~> predicateAccessPred ^^ PUnfold
  lazy val packageWand =
    "package" ~> exp ^^ PPackageWand
  lazy val applyWand =
    "apply" ~> magicWandExp ^^ PApplyWand
  lazy val inhale =
    ("inhale" | "assume") ~> exp ^^ PInhale
  lazy val exhale =
    "exhale" ~> exp ^^ PExhale
  lazy val assert =
    "assert" ~> exp ^^ PAssert
  lazy val localassign =
    idnuse ~ (":=" ~> exp) ^^ PVarAssign
  lazy val fieldassign =
    fieldAcc ~ (":=" ~> exp) ^^ PFieldAssign
  lazy val ifthnels =
    ("if" ~> "(" ~> exp <~ ")") ~ block ~ elsifEls ^^ {
      case cond ~ thn ~ els => PIf(cond, PSeqn(thn), els)
    }
  lazy val elsifEls: PackratParser[PStmt] = elsif | els
  lazy val elsif: PackratParser[PStmt] =
    ("elsif" ~> "(" ~> exp <~ ")") ~ block ~ elsifEls ^^ {
      case cond ~ thn ~ els => PIf(cond, PSeqn(thn), els)
    }
  lazy val els: PackratParser[PStmt] = opt("else" ~> block) ^^ { block => PSeqn(block.getOrElse(Nil)) }
  lazy val whle =
    ("while" ~> "(" ~> exp <~ ")") ~ rep(inv) ~ block ^^ {
      case cond ~ invs ~ body => PWhile(cond, invs, PSeqn(body))
    }
  lazy val varDecl =
    ("var" ~> idndef) ~ (":" ~> typ) ~ opt(":=" ~> exp) ^^ PLocalVarDecl
  lazy val letassDecl =
    ("define" ~> idndef) ~ exp ^^ PLetAss
  lazy val letwandDecl =
    ("wand" ~> idndef) ~ (":=" ~> exp) ^^ PLetWand
  lazy val fresh =
    "fresh" ~> repsep(idnuse, ",") ^^ {
      case vars => PFresh(vars)
    }
  lazy val constrainingBlock =
    ("constraining" ~> "(" ~> repsep(idnuse, ",") <~ ")") ~ block ^^ {
      case vars ~ s => PConstraining(vars, PSeqn(s))
    }
  lazy val newstmt =
    idnuse ~ (":=" ~> "new" ~> "(" ~> starOrFields <~ ")") ^^ PNewStmt
  lazy val starOrFields = (
      "*" ^^ (_ => None)
    | repsep(idnuse, ",") ^^ (fields => Some(fields)))
  lazy val lbl =
    idndef <~ ":" ^^ PLabel
  lazy val goto =
    "goto" ~> idnuse ^^ PGoto
  lazy val methodCall =
    opt(repsep(idnuse, ",") <~ ":=") ~ idnuse ~ parens(repsep(exp, ",")) ^^ {
      case None ~ method ~ args => PMethodCall(Nil, method, args)
      case Some(targets) ~ method ~ args => PMethodCall(targets, method, args)
    }

  // --- Types

  lazy val typ: PackratParser[PType] =
    primitiveTyp | domainTyp | seqType | setType | multisetType
  lazy val domainTyp: PackratParser[PDomainType] =
    idnuse ~ ("[" ~> (repsep(typ, ",") <~ "]")) ^^ PDomainType |
      idnuse ^^ {
        // domain type without type arguments (might also be a type variable)
        case name => PDomainType(name, Nil)
      }
  lazy val seqType: PackratParser[PType] =
    "Seq" ~ "[" ~> typ <~ "]" ^^ PSeqType
  lazy val setType: PackratParser[PType] =
    "Set" ~ "[" ~> typ <~ "]" ^^ PSetType
  lazy val multisetType: PackratParser[PType] =
    "Multiset" ~ "[" ~> typ <~ "]" ^^ PMultisetType
  lazy val primitiveTyp: PackratParser[PType] =
    ("Int" | "Bool" | "Perm" | "Ref") ^^ PPrimitiv

  // --- Expressions

  lazy val exp: PackratParser[PExp] =
    iteExpr
  lazy val iteExpr: PackratParser[PExp] =
    ((iffExp <~ "?") ~ iteExpr ~ (":" ~> iteExpr)) ^^ PCondExp | iffExp
  lazy val iffExp: PackratParser[PExp] =
    implExp ~ "<==>" ~ iffExp ^^ PBinExp | implExp
  lazy val implExp: PackratParser[PExp] =
    magicWandExp ~ "==>" ~ implExp ^^ PBinExp | magicWandExp

  lazy val magicWandExp: PackratParser[PExp] =
    realMagicWandExp | orExp
  lazy val realMagicWandExp: PackratParser[PExp] =
    orExp ~ "--*" ~ magicWandExp ^^ PBinExp

  lazy val orExp: PackratParser[PExp] =
    andExp ~ "||" ~ orExp ^^ PBinExp | andExp
  lazy val andExp: PackratParser[PExp] =
    cmpExp ~ "&&" ~ andExp ^^ PBinExp | cmpExp

  /* [2013-11-20 Malte]:
   * Consider the snippet
   *   var x: Int := 0
   *   inhale true
   * where it is important that the first line ends with an expression and the
   * second line starts with "inhale".
   * Remember that whitespaces and newlines are insignificant in SIL. The
   * parser will matche "0", and then it will try to match a binary operator
   * which might connect "0" with a second expression. Unfortunately, "in"
   * is a valid binary operator, and "hale" will be matched as the second
   * expression. This might sound odd because one might expect that a lexer
   * tokenized the second line into the tokens "inhale" and "true", and that
   * the parser should match whole tokens, not parts of them, part AFAIK, the
   * combinator parser we use does not consist of separate lexer and parser
   * phases, instead, parsing tries to consume as match as possible on a
   * per-character bases.
   *
   * A solution is to explicitly constrain the in-operator s.t. it may not
   * directly be followed by a character that is also valid in the middle of
   * an identifier (which are assumed to coincide with characters that may
   * occur in the middle of keywords). Notice that using "not(...)" is
   * important, because it yields a parser that doesn't actually consume
   * characters. This way, the parser effectively looks ahead to see if
   * it is really the in-operator that is coming, and if so, it actually
   * parses it.
   */
  lazy val cmpOp =
    "==" | "!=" | "<=" | ">=" | "<" | ">" |
    (not(s"in$identOtherLetter".r) ~> "in")

  lazy val cmpExp: PackratParser[PExp] =
    sum ~ cmpOp ~ sum ^^ PBinExp | sum

  lazy val sumOp = "++" | "+" | "-" | "union" | "intersection" | "setminus" | "subset"
  lazy val sum: PackratParser[PExp] =
    sum ~ sumOp ~ term ^^ PBinExp | term

  lazy val termOp = "*" | "/" | "\\" | "%"
  lazy val term: PackratParser[PExp] =
    term ~ termOp ~ suffixExpr ^^ PBinExp | suffixExpr

  lazy val suffixExpr: PackratParser[PExp] =
    atom ~ rep(suffix) ^^ {case fac ~ ss => foldPExp[PExp](fac, ss)}

  lazy val realSuffixExpr: PackratParser[PExp] =
    atom ~ rep1(suffix) ^^ {case fac ~ ss => foldPExp[PExp](fac, ss)}

  lazy val suffix: Parser[PExp => PExp] =
    "." ~> idnuse ^^ (id => (e: PExp) => PFieldAccess(e, id)) |
      "[.." ~> exp <~ "]" ^^ (n => (e: PExp) => PSeqTake(e, n)) |
      "[" ~> exp <~ "..]" ^^ (n => (e: PExp) => PSeqDrop(e, n)) |
      ("[" ~> exp <~ "..") ~ (exp <~ "]") ^^ {case n ~ m => (e: PExp) => PSeqDrop(PSeqTake(e, m), n)} |
      "[" ~> exp <~ "]" ^^ (e1 => (e0: PExp) => PSeqIndex(e0, e1)) |
      ("[" ~> exp <~ ":=") ~ (exp <~ "]") ^^ {case i ~ v => (e: PExp) => PSeqUpdate(e, i, v)}

  /* Atoms must (transitively) start with a literal or an identifier, but they
   * must not recurse with their first subrule!
   * Most general rule should come last, which is probably idnuse.
   */
  lazy val atom: PackratParser[PExp] =
    integer | bool | nul |
      old | pold | given |
      "result" ^^ (_ => PResultLit()) |
      ("-" | "!" | "+") ~ sum ^^ PUnExp |
      "(" ~> exp <~ ")" |
      accessPred |
      inhaleExhale |
      perm |
      quant |
      unfolding | folding | applying |
      setTypedEmpty | explicitSetNonEmpty |
      explicitMultisetNonEmpty | multiSetTypedEmpty |
      seqTypedEmpty | seqLength | explicitSeqNonEmpty | seqRange |
      fapp |
      idnuse

  lazy val accessPred: PackratParser[PAccPred] =
      "acc" ~> parens(locAcc ~ opt("," ~> exp)) ^^ {
        case loc ~ perms => PAccPred(loc, perms.getOrElse(PFullPerm()))
      }

  lazy val predicateAccessPred: PackratParser[PAccPred] =
    accessPred | predAcc ^^ {case loc => PAccPred(loc, PFullPerm())}

  lazy val fapp: PackratParser[PExp] =
    idnuse ~ parens(actualArgList) ^^ PFunctApp

  lazy val actualArgList: PackratParser[Seq[PExp]] =
    repsep(exp, ",")

  lazy val inhaleExhale: PackratParser[PExp] =
    ("[" ~> exp <~ ",") ~ (exp <~ "]") ^^ PInhaleExhaleExp

  lazy val perm: PackratParser[PExp] =
    "none" ^^ (_ => PNoPerm()) |
      "wildcard" ^^ (_ => PWildcard()) |
      "write" ^^ (_ => PFullPerm()) |
      "epsilon" ^^ (_ => PEpsilon()) |
      "perm" ~> parens(locAcc) ^^ PCurPerm

  lazy val quant: PackratParser[PExp] =
    ("forall" ~> formalArgList <~ "::") ~ rep(trigger) ~ exp ^^ PForall |
      ("exists" ~> formalArgList <~ "::") ~ exp ^^ PExists

  lazy val trigger: PackratParser[Seq[PExp]] =
    "{" ~> repsep(exp, ",") <~ "}"

  lazy val old: PackratParser[PExp] =
    "old" ~> parens(exp) ^^ POld

  lazy val pold: PackratParser[PExp] =
    "now" ~> parens(exp) ^^ PPackageOld

  lazy val given: PackratParser[PExp] =
    "lhs" ~> parens(exp) ^^ PApplyOld

  lazy val locAcc: PackratParser[PLocationAccess] =
    fieldAcc | predAcc

  lazy val fieldAcc: PackratParser[PFieldAccess] =
    realSuffixExpr ^? ({
      case fa: PFieldAccess => fa
    }, _ => "Field expected")

  lazy val predAcc: PackratParser[PPredicateAccess] =
    idnuse ~ parens(actualArgList) ^^ {case id ~ args => PPredicateAccess(args, id)}

  lazy val unfolding: PackratParser[PExp] =
    ("unfolding" ~> predicateAccessPred) ~ ("in" ~> exp) ^^ PUnfolding

  lazy val folding: PackratParser[PExp] =
    ("folding" ~> predicateAccessPred) ~ ("in" ~> exp) ^^ PFolding

  lazy val applying: PackratParser[PExp] =
    /* We must be careful here to not create ambiguities in our granmmar.
     * when 'magicWandExp' is used instead of the more specific
     * 'realMagicWandExp | idnuse', then the following problem can occur:
     * Consider an expression such as "applying w in A". The parser
     * will interpret "w in A" as a set-contains expression, which is
     * fine according to our rules. The outer applying-rule will the fail.
     * I suspect that NOT using a memoising packrat parser would help
     * here, because the failing applying-rule should backtrack enough
     * to reparse "w in A", but this time as desired, not as a
     * set-contains expression. This is just an assumption, however,
     * and implementing would mean that we have to rewrite the
     * left-recursive parsing rules (are these only sum and term?).
     * Moreover, not using a memoising parser might make the parser
     * significantly slower.
     */
    ("applying" ~> ("(" ~> realMagicWandExp <~ ")" | idnuse)) ~ ("in" ~> exp) ^^ PApplying

  lazy val integer =
    "[0-9]+".r ^^ (s => PIntLit(BigInt(s)))

  lazy val bool =
    "true" ^^ (_ => PBoolLit(b = true)) |
      "false" ^^ (_ => PBoolLit(b = false))

  lazy val nul =
    "null" ^^ (_ => PNullLit())

  lazy val idndef =
    ident ^^ PIdnDef

  lazy val idnuse =
    ident ^^ PIdnUse

  // --- Sequence and set atoms

  lazy val seqLength: PackratParser[PExp] =
    "|" ~> exp <~ "|" ^^ PSize

  lazy val seqTypedEmpty: PackratParser[PExp] =
    "Seq[" ~> typ <~ "]()" ^^ PEmptySeq

  lazy val explicitSeqNonEmpty: PackratParser[PExp] =
    "Seq(" ~> rep1sep(exp, ",") <~ ")" ^^ {
//      case Nil => PEmptySeq(PUnknown())
      case elems => PExplicitSeq(elems)
    }

  lazy val seqRange: PackratParser[PExp] =
    ("[" ~> exp <~ "..") ~ (exp <~ ")") ^^ PRangeSeq

  lazy val setTypedEmpty: PackratParser[PExp] =
    "Set" ~ "[" ~> typ <~ "]" ~ "(" ~ ")" ^^ PEmptySet

  lazy val explicitSetNonEmpty: PackratParser[PExp] =
    "Set" /*~ opt("[" ~> typ <~ "]")*/ ~ "(" ~> rep1sep(exp, ",") <~ ")" ^^ PExplicitSet
/*      {
      case (None,s) => PExplicitSet(s)
      case (Some(t),s) => { val p = PExplicitSet(s,t);}
    }*/

  lazy val multiSetTypedEmpty: PackratParser[PExp] =
    "Multiset" ~ "[" ~> typ <~ "]" ~ "("~")" ^^ PEmptyMultiset

  lazy val explicitMultisetNonEmpty: PackratParser[PExp] =
    "Multiset" ~ "(" ~> rep1sep(exp, ",") <~ ")" ^^ {
      case elems => PExplicitMultiset(elems)
    }

  // --- Identifier and keywords

  /* See
   *   http://code.google.com/p/kiama/wiki/ParserCombs#Identifiers
   * for an explanation of "keywords(...)" and why we need it.
   * The gist of it is, that we want to support identifiers that start with a
   * keyword, for example "index".
   */

  val ident =
    not(keyword) ~> identifier.r |
      failure("identifier expected")

  val identFirstLetter = "[a-zA-Z$_]"

  val identOtherLetterChars = "a-zA-Z0-9$_'"
  val identOtherLetter = s"[$identOtherLetterChars]"
  val identOtherLetterNeg = s"[^$identOtherLetterChars]"

  val identifier = identFirstLetter + identOtherLetter + "*"

  val keyword = keywords(identOtherLetterNeg.r, reserved)

  private def foldPExp[E <: PExp](e: PExp, es: List[PExp => E]): E =
    es.foldLeft(e){(t, a) =>
      val result = a(t)
      result.setPos(t)
      result
    }.asInstanceOf[E]
}
