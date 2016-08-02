
/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import java.nio.file.Path

import org.kiama.util.Positions._
import org.kiama.util.WhitespacePositionedParserUtilities
import viper.silver.ast._
import viper.silver.verifier.ParseError

import scala.collection.immutable.Iterable
import scala.collection.mutable
import scala.language.implicitConversions
import scala.language.reflectiveCalls

import viper.silver.verifier._

/**
  * A parser for the SIL language that takes a string and produces an intermediate
  * AST ([[viper.silver.parser.PNode]]), or a parse error.  The intermediate AST can
  * then be type-checked and translated into the SIL AST ([[viper.silver.ast.Node]])
  * using [[viper.silver.parser.Translator]].
  *
  * IMPORTANT: If you change or extend the syntax, please also update the syntax
  * description in documentation/syntax as well as the syntax highlighting definitions
  * in util/highlighting!
  *
  * IMPORTANT: Also keep the parser in sync with the pretty printer!
  */
object Parser extends BaseParser {
  override def file = _file
  var _file: Path = null
  var _imports: mutable.HashMap[Path, Boolean] = null

  def parse(s: String, f: Path) = {
    _file = f
    _imports = mutable.HashMap((f, true))
    val rp = RecParser(f)
    rp.parse(s) match {
      case rp.Success(a, b) => Success(a, b)
      case rp.Failure(a, b) => Failure(a, b)
      case rp.Error(a, b) => Error(a, b)
    }
  }

  case class RecParser(file: Path) extends BaseParser {
    def parse(s: String) = parseAll(parser, s)
  }
}

/**
  * ATG: Kiama does not support AST node positions with files.
  * MultiFileParserPosition is a workaround case class which extends util.parsing.input.Position
  * and provides the missing field (file) from the AbstractSourcePosition trait.
  */
case class FilePosition(file: Path, pos: util.parsing.input.Position)
  extends util.parsing.input.Position with HasLineColumn
{
  override lazy val line = pos.line
  override lazy val column = pos.column
  override lazy val lineContents = toString
  override lazy val toString = s"${file.getFileName}@$pos"
}

/**
  * A parser intended for debugging. Extend it and make parsing rules log their invocation
  * by changing a rule such as
  *   lazy val foo = body
  * to
  *   lazy val foo = "foo" !!! body
  *
  * Taken from http://jim-mcbeath.blogspot.be/2011/07/debugging-scala-parser-combinators.html
  */

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

      DebuggingParser.depth -= 1

      t
    }
  }

  implicit def toWrapped(name: String): AnyRef = new {
    def !!![T](p: Parser[T]) = new Wrap(name,p)
  }
}


/**
  * This parser is a PackratParser and thus CAN support left recursive parsing
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

  override def parseAndPosition[T] (f : Input => ParseResult[T], in : Input) : ParseResult[T] =
    f (in) match {
      case res @ Success (t, in1) =>
        val startoffset = handleWhiteSpace (in)
        val newin = in.drop (startoffset - in.offset)
        setStart (t, FilePosition(file, newin.pos))
        setStartWhite (t, FilePosition(file, in.pos))
        setFinish (t, FilePosition(file, in1.pos))
        res
      case res =>
        res
    }

  /** The file we are currently parsing (for creating positions later). */
  def file: Path

  /** A helper method for wrapping keywords so that identifiers that have a keyword as their
    *  prefix are parsed correctly.
    */
  private def keyword(identifier: String) = not(s"$identifier$identOtherLetter".r) ~> identifier

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
    "Int", "Perm", "Bool", "Ref", "Rational",
    // boolean constants
    "true", "false",
    // null
    "null",
    // preamble importing
    "import",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom", "var", "returns", "field", "define", "wand",
    // specifications
    "requires", "ensures", "invariant",
    // statements
    "fold", "unfold", "inhale", "exhale", "new", "assert", "assume", "package", "apply",
    // control flow
    "while", "if", "elseif", "else", "goto", "label",
    // special fresh block
    "fresh", "constraining",
    // sequences
    "Seq",
    // sets and multisets
    "Set", "Multiset", "union", "intersection", "setminus", "subset",
    // prover hint expressions
    "unfolding", "in", "folding", "applying", "packaging",
    // old expression
    "old", "lhs",
    // other expressions
    "let",
    // quantification
    "forall", "exists", "forperm",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique"/*,

    // TODO: Hacks to stop the parser from interpreting, e.g., "inhale" as "in hale"
    "variant", "hale", "tersection"*/
  )

  lazy val parser: PackratParser[PProgram] = phrase(programDecl)

  // --- Whitespace

  lazy val whitespaceParser: PackratParser[Any] =
    rep(whiteSpace | comment)

  lazy val comment: PackratParser[Any] =
    ("/*" ~ rep(not("*/") ~ (comment | any)) ~ "*/") |
      ("//" ~ rep(not("\n") ~ any))

  // --- Declarations

  lazy val programDecl =
    rep(preambleImport | defineDecl | domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl) ^^ {
      case decls =>
        var globalDefines: Seq[PDefine] = decls.collect { case d: PDefine => d }
        globalDefines = expandDefines(globalDefines, globalDefines)

        val imports: List[PImport] = decls.collect { case i: PImport => i }

        val dups: Iterable[ParseError] = imports.groupBy(identity).collect {
          case (imp@ PImport(x), List(_,_,_*)) =>
            val dup_pos = imp.start.asInstanceOf[viper.silver.ast.Position]
            val report = s"""multiple imports of the same file "$x" detected"""
            //println(s"warning: $report ($dup_pos)")
            ParseError(report, dup_pos)
        }

        //println(s"imports in current file: $imports")
        //println(s"all imports: ${viper.silver.parser.Parser._imports}")

        val imp_progs_results: List[Either[ParseReport, Any] with Product with Serializable] = imports.collect {
          case imp@ PImport(imp_file) =>
            val imp_path = java.nio.file.Paths.get(file.getParent + "/" + imp_file)
            val imp_pos = imp.start.asInstanceOf[viper.silver.ast.Position]

            if (java.nio.file.Files.notExists(imp_path))
              Left(ParseError(s"""file "$imp_path" does not exist""", imp_pos))

            else if (java.nio.file.Files.isSameFile(imp_path, file))
              Left(ParseError(s"""importing yourself is probably not a good idea!""", imp_pos))

            else if (viper.silver.parser.Parser._imports.put(imp_path, true).isEmpty) {
              val source = scala.io.Source.fromFile(imp_path.toString)
              val buffer = try {
                Right(source.getLines.toArray)
              } catch {
                case e@(_: RuntimeException | _: java.io.IOException) =>
                  Left(ParseError(s"""could not import file ($e)""", imp_pos))
              } finally {
                source.close()
              }
              buffer match {
                case Left(e) => Left(e)
                case Right(s) =>
                  //TODO print debug info iff --dbg switch is used
                  //println(s"@importing $imp_file into $file")

                  val p = viper.silver.parser.Parser.RecParser(imp_path)
                  p.parse(s.mkString("\n") + "\n") match {
                    case p.Success(a, _) => Right(a)
                    case p.Failure(msg, next) => Left(ParseError(s"Failure: $msg", FilePosition(imp_path, next.pos)))
                    case p.Error(msg, next) => Left(ParseError(s"Error: $msg", FilePosition(imp_path, next.pos)))
                  }
              }
            }

            else {
              val report = s"found loop dependency among these imports:\n" +
                viper.silver.parser.Parser._imports.map {case (k,v)=>k} .mkString("\n")
              println(s"warning: $report\n(loop starts at $imp_pos)")
              Right(ParseWarning(report, imp_pos))
            }
        }

        val imp_progs = imp_progs_results.collect { case Right(p) => p }

        val imp_reports = imp_progs_results.collect { case Left(e) => e } ++
          imp_progs.collect { case PProgram(_, _, _, _, _, _, e: List[ParseReport]) => e }.flatten ++
            dups

        val files =
          imp_progs.collect { case PProgram(f: List[PImport], _, _, _, _, _, _) => f }.flatten ++
            imports

        val domains =
          imp_progs.collect { case PProgram(_, d: List[PDomain], _, _, _, _, _) => d }.flatten ++
            decls.collect { case d: PDomain => expandDefines(globalDefines, d) }

        val fields =
          imp_progs.collect { case PProgram(_, _, f: List[PField], _, _, _, _) => f }.flatten ++
            decls.collect { case f: PField => f }

        val functions =
          imp_progs.collect { case PProgram(_, _, _, f: List[PFunction], _, _, _) => f }.flatten ++
            decls.collect { case d: PFunction => expandDefines(globalDefines, d) }

        val predicates =
          imp_progs.collect { case PProgram(_, _, _, _, p: List[PPredicate], _, _) => p }.flatten ++
            decls.collect { case d: PPredicate => expandDefines(globalDefines, d) }

        val methods =
          imp_progs.collect { case PProgram(_, _, _, _, _, m: List[PMethod], _) => m }.flatten ++
            decls.collect {
              case meth: PMethod =>
                var localDefines = meth.deepCollect {case n: PDefine => n}
                localDefines = expandDefines(localDefines ++ globalDefines, localDefines)

                val methWithoutDefines =
                  if (localDefines.isEmpty)
                    meth
                  else
                    meth.transform { case la: PDefine => PSkip().setPos(la) }()

                expandDefines(localDefines ++ globalDefines, methWithoutDefines)
            }

        PProgram(files, domains, fields, functions, predicates, methods, imp_reports)
    }

  lazy val fieldDecl =
    ("field" ~> idndef) ~ (":" ~> typ <~ opt(";")) ^^ PField

  lazy val methodDecl =
    methodSignature ~ rep(pre) ~ rep(post) ~ opt(block) ^^ {
      case name ~ args ~ rets ~ pres ~ posts ~ Some(body) =>
        PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(body))
      case name ~ args ~ rets ~ pres ~ posts ~ None =>
        PMethod(name, args, rets.getOrElse(Nil), pres, posts, PSeqn(Seq(PInhale(PBoolLit(b = false)))))
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
  lazy val nonEmptyFormalArgList =
    rep1sep(formalArg, ",")
  lazy val formalArg =
    idndef ~ (":" ~> typ) ^^ PFormalArgDecl

  lazy val functionDecl =
    functionSignature ~ rep(pre) ~ rep(post) ~ opt("{" ~> (exp <~ "}")) ^^ PFunction
  lazy val functionSignature =
    ("function" ~> idndef) ~ ("(" ~> formalArgList <~ ")") ~ (":" ~> typ)

  lazy val domainFunctionDecl = opt("unique") ~ (functionSignature <~ opt(";")) ^^ {
    case unique ~ fdecl =>
      fdecl match {
        case name ~ formalArgs ~ t => PDomainFunction1(name, formalArgs, t, unique.isDefined)
      }
  }

  lazy val predicateDecl =
    ("predicate" ~> idndef) ~ ("(" ~> formalArgList <~ ")") ~ opt("{" ~> (exp <~ "}")) ^^ PPredicate

  lazy val domainDecl =
    ("domain" ~> idndef) ~
      opt("[" ~> repsep(domainTypeVarDecl, ",") <~ "]") ~
      ("{" ~> rep(domainFunctionDecl)) ~
      (rep(axiomDecl) <~ "}") ^^ {
      case name ~ typparams ~ funcs ~ axioms =>
        PDomain(
          name,
          typparams.getOrElse(Nil),
          funcs map (f => PDomainFunction(f.idndef,f.formalArgs,f.typ,f.unique)(PIdnUse(name.name)).setPos(f)),
          axioms map (a=>PAxiom(a.idndef,a.exp)(PIdnUse(name.name)).setPos(a)))
    }

  lazy val domainTypeVarDecl =
    idndef ^^ PTypeVarDecl

  lazy val axiomDecl =
    ("axiom" ~> idndef) ~ ("{" ~> (exp <~ "}")) <~ opt(";") ^^ PAxiom1

  // --- Statements

  def parens[A](p: Parser[A]) = "(" ~> p <~ ")"
  def quoted[A](p: Parser[A]) = "\"" ~> p <~ "\""

  lazy val relativeFilePath =
    "\\A[~.]?(?:\\/?[.\\w-\\s])+".r

  lazy val preambleImport =
    keyword("import") ~> quoted(relativeFilePath) ^^ {
      case filename =>
        PImport(filename)
    }

  lazy val block: Parser[Seq[PStmt]] =
    "{" ~> (stmts <~ "}")
  lazy val stmts =
    rep(stmt <~ opt(";"))
  lazy val stmt =
    fieldassign | localassign | fold | unfold | exhale | assert |
      inhale | ifthnels | whle | varDecl | defineDecl | letwandDecl | newstmt | fresh | constrainingBlock |
      methodCall | goto | lbl | packageWand | applyWand

  lazy val fold =
    "fold" ~> predicateAccessPred ^^ PFold
  lazy val unfold =
    "unfold" ~> predicateAccessPred ^^ PUnfold
  lazy val packageWand =
    "package" ~> magicWandExp ^^ PPackageWand
  lazy val applyWand =
    "apply" ~> magicWandExp ^^ PApplyWand
  lazy val inhale =
    (keyword("inhale") | keyword("assume")) ~> exp ^^ PInhale
  lazy val exhale =
    keyword("exhale") ~> exp ^^ PExhale
  lazy val assert =
    keyword("assert") ~> exp ^^ PAssert
  lazy val localassign =
    idnuse ~ (":=" ~> exp) ^^ PVarAssign
  lazy val fieldassign =
    fieldAcc ~ (":=" ~> exp) ^^ PFieldAssign
  lazy val ifthnels =
    ("if" ~> "(" ~> exp <~ ")") ~ block ~ elsifEls ^^ {
      case cond ~ thn ~ ele => PIf(cond, PSeqn(thn), ele)
    }
  lazy val elsifEls: PackratParser[PStmt] = elsif | els
  lazy val elsif: PackratParser[PStmt] =
    ("elseif" ~> "(" ~> exp <~ ")") ~ block ~ elsifEls ^^ {
      case cond ~ thn ~ ele => PIf(cond, PSeqn(thn), ele)
    }
  lazy val els: PackratParser[PStmt] = opt("else" ~> block) ^^ { block => PSeqn(block.getOrElse(Nil)) }
  lazy val whle =
    ("while" ~> "(" ~> exp <~ ")") ~ rep(inv) ~ block ^^ {
      case cond ~ invs ~ body => PWhile(cond, invs, PSeqn(body))
    }
  lazy val varDecl =
    ("var" ~> idndef) ~ (":" ~> typ) ~ opt(":=" ~> exp) ^^ PLocalVarDecl
  lazy val defineDecl =
    ("define" ~> idndef) ~ opt("(" ~> repsep(idndef, ",") <~ ")") ~ (exp | block) ^^ {
      case iddef ~ args ~ (e: PExp) => PDefine(iddef, args, e)
      case iddef ~ args ~ (ss: Seq[PStmt] @unchecked) => PDefine(iddef, args, PSeqn(ss))
    }
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
    keyword("label") ~> idndef ^^ PLabel
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
    "Rational" ^^ { case _ => PPrimitiv("Perm") } |
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

  /* Magic wands can be
   *  - wand literals, e.g., 'true --* true'
   *  - wand chunk terms, e.g, 'w', where 'wand w := ...'
   */
  lazy val magicWandExp: PackratParser[PExp] =
    realMagicWandExp | orExp
  lazy val realMagicWandExp: PackratParser[PBinExp] =
    orExp ~ "--*" ~ magicWandExp ^^ PBinExp

  lazy val orExp: PackratParser[PExp] =
    andExp ~ "||" ~ orExp ^^ PBinExp | andExp
  lazy val andExp: PackratParser[PExp] =
    eqExp ~ "&&" ~ andExp ^^ PBinExp | eqExp

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
  lazy val eqOp = "==" | "!="

  lazy val eqExp: PackratParser[PExp] =
    cmpExp ~ eqOp ~ eqExp ^^ PBinExp | cmpExp


  lazy val cmpOp = "<=" | ">=" | "<" | ">" | keyword("in")

  lazy val cmpExp: PackratParser[PExp] =
    sum ~ cmpOp ~ cmpExp ^^ PBinExp | sum

  lazy val sumOp =
    "++" |
    "+" |
    "-" |
    keyword("union") |
    keyword("intersection") |
    keyword("setminus") |
    keyword("subset")
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
      old | applyOld |
      keyword("result") ^^ (_ => PResultLit()) |
      ("-" | "!" | "+") ~ sum ^^ PUnExp |
      "(" ~> exp <~ ")" |
      accessPred |
      inhaleExhale |
      perm |
      let |
      quant | forperm |
      unfolding | folding | applying | packaging |
      setTypedEmpty | explicitSetNonEmpty |
      explicitMultisetNonEmpty | multiSetTypedEmpty |
      seqTypedEmpty | seqLength | explicitSeqNonEmpty | seqRange |
      fapp | typedFapp |
      idnuse

  lazy val accessPred: PackratParser[PAccPred] =
      "acc" ~> parens(locAcc ~ opt("," ~> exp)) ^^ {
        case loc ~ perms => PAccPred(loc, perms.getOrElse(PFullPerm()))
      }

  lazy val predicateAccessPred: PackratParser[PAccPred] =
    accessPred | predAcc ^^ {case loc => PAccPred(loc, PFullPerm())}

  lazy val typedFapp: PackratParser[PExp] =
    parens(idnuse ~ parens(actualArgList) ~ (":" ~> typ)) ^^ {
      case func ~ args ~ typeGiven => PFunctApp(func,args,Some(typeGiven))
    }

  lazy val fapp: PackratParser[PExp] =
    idnuse ~ parens(actualArgList) ^^ {
      case func ~ args => PFunctApp(func,args,None)
    }


  lazy val actualArgList: PackratParser[Seq[PExp]] =
    repsep(exp, ",")

  lazy val inhaleExhale: PackratParser[PExp] =
    ("[" ~> exp <~ ",") ~ (exp <~ "]") ^^ PInhaleExhaleExp

  lazy val perm: PackratParser[PExp] =
    keyword("none") ^^ (_ => PNoPerm()) |
    keyword("wildcard") ^^ (_ => PWildcard()) |
    keyword("write") ^^ (_ => PFullPerm()) |
    keyword("epsilon") ^^ (_ => PEpsilon()) |
    "perm" ~> parens(locAcc) ^^ PCurPerm

  lazy val quant: PackratParser[PExp] =
    (keyword("forall") ~> nonEmptyFormalArgList <~ "::") ~ rep(trigger) ~ exp ^^ PForall |
    (keyword("exists") ~> nonEmptyFormalArgList <~ "::") ~ exp ^^ PExists

  lazy val forperm: PackratParser[PExp] =
    (keyword("forperm") ~> "[" ~> repsep(idnuse,",") <~ "]") ~ idndef ~ ("::" ~> exp) ^^ {
      case ids ~ id ~ body => PForPerm(PFormalArgDecl(id, PPrimitiv("Ref")), ids, body)
    }

  lazy val trigger: PackratParser[Seq[PExp]] =
    "{" ~> repsep(exp, ",") <~ "}"

  lazy val old: PackratParser[PExp] =
    "old" ~> (parens(exp) ^^ POld |
      ("[" ~> idnuse <~ "]") ~ parens(exp) ^^ PLabelledOld)

  lazy val applyOld: PackratParser[PExp] =
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
    ("folding" ~> predicateAccessPred) ~ ("in" ~> exp) ^^ PFoldingGhostOp

  lazy val applying: PackratParser[PExp] =
    /* We must be careful here to not create ambiguities in our grammar.
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
    ("applying" ~> ("(" ~> realMagicWandExp <~ ")" | idnuse)) ~ ("in" ~> exp) ^^ PApplyingGhostOp

  lazy val packaging: PackratParser[PExp] =
    /* See comment on applying */
    ("packaging" ~> ("(" ~> realMagicWandExp <~ ")" | idnuse)) ~ ("in" ~> exp) ^^ PPackagingGhostOp

  lazy val let: PackratParser[PExp] =
    ("let" ~> idndef <~ "==") ~ ("(" ~> exp <~ ")") ~ ("in" ~> exp) ^^ { case id ~ exp1 ~ exp2 =>
      /* Type unresolvedType is expected to be replaced with the type of exp1
       * after the latter has been resolved
       * */
      val unresolvedType = PUnknown().setPos(id)
      val formalArgDecl = PFormalArgDecl(id, unresolvedType).setPos(id)
      val nestedScope = PLetNestedScope(formalArgDecl, exp2).setPos(exp2)

      PLet(exp1, nestedScope)
    }

  lazy val integer =
    "[0-9]+".r ^^ (s => PIntLit(BigInt(s)))

  lazy val bool =
    keyword("true") ^^ (_ => PBoolLit(b = true)) |
    keyword("false") ^^ (_ => PBoolLit(b = false))

  lazy val nul =
    keyword("null") ^^ (_ => PNullLit())

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

  //We assume the symbol "#" cannot occur in using given identifiers
  val identFirstLetter = "[a-zA-Z$_]"

  val identOtherLetterChars = "a-zA-Z0-9$_'"
  val identOtherLetter = s"[$identOtherLetterChars]"
  val identOtherLetterNeg = s"[^$identOtherLetterChars]"

  val identifier = identFirstLetter + identOtherLetter + "*"

  val keyword = keywords(identOtherLetterNeg.r, reserved)

  val ident =
    not(keyword) ~> identifier.r |
      identifier.r >> { a => failure(s"identifier expected, but keyword `$a' found") }

  private def foldPExp[E <: PExp](e: PExp, es: List[PExp => E]): E =
    es.foldLeft(e){(t, a) =>
      val result = a(t)
      result.setPos(t)
      result
    }.asInstanceOf[E]

  private def expandDefines(defines: Seq[PDefine], toExpand: Seq[PDefine]): Seq[PDefine] = {
    val maxCount = 25
      /* TODO: Totally arbitrary cycle breaker. We should properly detect
       * (mutually) recursive named assertions.
       */
    var count = 0
    var definesToExpand = toExpand
    var expandedIds = Seq[String]()

    do {
      expandedIds = Seq.empty
      count += 1

      definesToExpand = definesToExpand.map(define => {
        val optExpandedDefine = doExpandDefines[PDefine](defines, define)
        expandedIds = optExpandedDefine.map(_.idndef.name).toSeq ++ expandedIds

        optExpandedDefine.getOrElse(define)
      })
    } while (expandedIds.nonEmpty && count <= maxCount)

    if (count > maxCount)
      sys.error(  s"Couldn't expand all named assertions in $maxCount cycles. "
                + s"Might there be a mutual recursion involving $expandedIds?")

    definesToExpand
  }

  @inline
  private def expandDefines[N <: PNode](defines: Seq[PDefine], node: N): N =
    doExpandDefines(defines, node).getOrElse(node)

  private def doExpandDefines[N <: PNode](defines: Seq[PDefine], node: N): Option[N] = {
    var expanded = false

    def lookupOrElse(piu: PIdnUse, els: PNode) =
      defines.find(_.idndef.name == piu.name).fold[PNode](els) _

    def expandAllegedInvocation(target: PIdnUse, targetArgs: Seq[PExp], els: PNode): PNode = {
      /* Potentially expand a named assertion that takes arguments, e.g. A(x, y) */
      lookupOrElse(target, els)(define => define.args match {
        case None =>
          /* There is a named assertion with name `target`, but the named
           * assertion takes arguments. Hence, `target` cannot denote the
           * use of a named assertion.
           */
          els
        case Some(args) if targetArgs.length != args.length =>
          /* Similar to the previous case */
          els
        case Some(args) =>
          expanded = true

          define.body.transform {
            /* Expand the named assertion's formal arguments by the given actual arguments */
            case piu: PIdnUse =>
              args.indexWhere(_.name == piu.name) match {
                case -1 => piu
                case i => targetArgs(i)
              }
          }() : PNode /* [2014-06-31 Malte] Type-checker wasn't pleased without it */
      })
    }

    val potentiallyExpandedNode =
      node.transform {
        case piu: PIdnUse =>
          /* Potentially expand a named assertion that takes no arguments, e.g. A.
           * If piu (which is a symbol) denotes a named assertion (i.e. if there
           * is a define in defines whose name is piu), then it is replaced by
           * the body of the named assertion.
           */
          lookupOrElse(piu, piu)(define => {
            expanded = true

            define.body
          })

        case fapp: PFunctApp => expandAllegedInvocation(fapp.func, fapp.args, fapp)
        case call: PMethodCall => expandAllegedInvocation(call.method, call.args, call)
      }(recursive = _ => true)

    if (expanded) Some(potentiallyExpandedNode)
    else None
  }
}
