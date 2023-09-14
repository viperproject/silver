// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.net.URL
import java.nio.file.{Path, Paths}
import viper.silver.ast.{FilePosition, LabelledOld, LineCol, NoPosition, Position, SourcePosition}
import viper.silver.ast.utility.{DiskLoader, FileLoader}
import viper.silver.parser.FastParserCompanion.{LW, LeadingWhitespace}
import viper.silver.plugin.{ParserPluginTemplate, SilverPluginManager}
import viper.silver.verifier.{ParseError, ParseWarning}

import scala.collection.{immutable, mutable}
import scala.util.{Failure, Success}
import viper.silver.ast.HasLineColumn

case class ParseException(msg: String, pos: (Position, Position)) extends Exception

case class SuffixedExpressionGenerator[+E <: PExp](func: PExp => E) extends (PExp => PExp) {
  override def apply(v1: PExp): E = func(v1)
}

object FastParserCompanion {
  import fastparse._

  val whitespaceWithoutNewlineOrComments = {
    import NoWhitespace._
    implicit ctx: ParsingRun[_] =>
      NoTrace((" " | "\t").rep)
  }

  implicit val whitespace = {
    import NoWhitespace._
    implicit ctx: ParsingRun[_] =>
      NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  class LeadingWhitespace[T](val p: () => P[T]) extends AnyVal {
    /**
      * Using `p.lw` is shorthand for `Pass ~ p` (the same parser but with possibly leading whitespace).
      *
      * A parser of the form `FP(p0 ~ p1.?)` or `FP(p0 ~ p2.rep)` may return an end position which
      * includes trailing whitespaces (incl. comments, newlines) if `p1` or `p2` fail to match (the `~` does this).
      * Instead we would like to use `FP(p0 ~~ (Pass ~ p1).?)` or `FP(p0 ~~ (Pass ~ p2).rep)`, which avoids this issue.
      */
    def lw(implicit ctx: P[Any]): LW[T] = new LW(() => Pass ~ p())
    def ~~~[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~ other.p()).asInstanceOf[P[R]]
    def ~~~/[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~/ other.p()).asInstanceOf[P[R]]
  }
  /**
    * A parser which matches leading whitespaces. See `LeadingWhitespace.lw` for more info. Can only be operated on in
    * restricted ways (e.g. `?`, `rep`, `|` or `map`), requiring that it is eventually appened to a normal parser (of type `P[V]`).
    *
    * For example, the following two are equivalent:
    * {{{FP("hello" ~~~ "world".lw.?)
    * FP("hello" ~~ (Pass ~ "world").?)}}}
    * The type system prevents one from erroneously writing:
    * {{{FP("hello" ~ "world".lw.?)}}}
    */
  class LW[T](val p: () => P[T]) {
    def ?[V](implicit optioner: Implicits.Optioner[T, V], ctx: P[Any]): LW[V] = new LW(() => p().?.asInstanceOf[P[V]])
    def rep[V](implicit repeater: Implicits.Repeater[T, V], ctx: P[Any]): LW[V] = new LW(() => p().rep.asInstanceOf[P[V]])
    def |[V >: T](other: LW[V])(implicit ctx: P[Any]): LW[V] = new LW(() => (p() | other.p()).asInstanceOf[P[V]])
    def map[V](f: T => V): LW[V] = new LW(() => p().map(f))
  }

  val basicKeywords = immutable.Set("result",
    // types
    "Int", "Perm", "Bool", "Ref", "Rational",
    // boolean constants
    "true", "false",
    // null
    "null",
    // preamble importing
    "import",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom", "var", "returns", "field", "define", "interpretation",
    // specifications
    "requires", "ensures", "invariant",
    // statements
    "fold", "unfold", "inhale", "exhale", "new", "assert", "assume", "package", "apply", "quasihavoc", "quasihavocall",
    // control flow
    "while", "if", "elseif", "else", "goto", "label",
    // sequences
    "Seq",
    // sets and multisets
    "Set", "Multiset", "union", "intersection", "setminus", "subset",
    // maps
    "Map", "range",
    // prover hint expressions
    "unfolding", "in", "applying",
    // old expression
    "old", "lhs",
    // other expressions
    "let",
    // quantification
    "forall", "exists", "forperm",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique")
}

class FastParser {
  import fastparse._

  implicit val whitespace = {
    import NoWhitespace._
    implicit ctx: ParsingRun[_] =>
      NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  val lineCol = new LineCol(this)

  /* When importing a file from standard library, e.g. `include <inc.vpr>`, the file is expected
   * to be located in `resources/${standard_import_directory}`, e.g. `resources/import/inv.vpr`.
   */
  val standard_import_directory = "import"

  var _line_offset: Array[Int] = null
  /** The file we are currently parsing (for creating positions later). */
  var _file: Path = null
  private var _warnings: Seq[ParseWarning] = Seq()

  def parse(s: String, f: Path, plugins: Option[SilverPluginManager] = None, loader: FileLoader = DiskLoader) = {
    // Strategy to handle imports
    // Idea: Import every import reference and merge imported methods, functions, imports, .. into current program
    //       iterate until no new imports are present.
    //       To import each file at most once the absolute path is normalized (removes redundancies).
    //       For standard import the path relative to the import folder (in resources) is normalized and used.
    //       (normalize a path is a purely syntactic operation. if sally were a symbolic link removing sally/.. might
    //       result in a path that no longer locates the intended file. toRealPath() might be an alternative)

    def resolveImports(p: PProgram) = {
      val localsToImport = new mutable.ArrayBuffer[Path]()
      val localImportStatements = new mutable.HashMap[Path, PImport]()
      val standardsToImport = new mutable.ArrayBuffer[Path]()
      val standardImportStatements = new mutable.HashMap[Path, PImport]()

      // assume p is a program from the user space (local).
      val filePath = f.toAbsolutePath.normalize()
      localsToImport.append(filePath)

      var imports = p.imports
      var macros = p.macros
      var domains = p.domains
      var fields = p.fields
      var functions = p.functions
      var methods = p.methods
      var predicates = p.predicates
      var extensions = p.extensions
      var errors = p.errors

      def appendNewImports(imports: Seq[PImport], current: Path, fromLocal: Boolean): Unit = {
        for (ip <- imports) {
          if (ip.local) {
            val localPath = current.resolveSibling(ip.file.s).normalize()
            if (fromLocal) {
              if(!localsToImport.contains(localPath)){
                ip.resolved = Some(localPath)
                localsToImport.append(localPath)
                localImportStatements.update(localPath, ip)
              }
            } else {
              // local import get transformed to standard imports
              if (!standardsToImport.contains(localPath)) {
                ip.resolved = Some(localPath)
                ip.local = false
                standardsToImport.append(localPath)
                standardImportStatements.update(localPath, ip)
              }
            }
          } else {
            val standardPath = Paths.get(ip.file.s).normalize()
            if(!standardsToImport.contains(standardPath)){
              ip.resolved = Some(standardPath)
              standardsToImport.append(standardPath)
              standardImportStatements.update(standardPath, ip)
            }
          }
        }
      }

      def appendNewProgram(newProg: PProgram): Unit = {
        imports ++= newProg.imports
        macros ++= newProg.macros
        domains ++= newProg.domains
        fields ++= newProg.fields
        functions ++= newProg.functions
        methods ++= newProg.methods
        predicates ++= newProg.predicates
        extensions ++= newProg.extensions
        errors ++= newProg.errors
      }

      appendNewImports(p.imports, filePath, true)

      // resolve imports from imported programs
      var i = 1 // localsToImport
      var j = 0 // standardsToImport
      while (i < localsToImport.length || j < standardsToImport.length) {
        // at least one local or standard import has not yet been resolved
        if (i < localsToImport.length){
          // import a local file

          val current = localsToImport(i)
          val newProg = importLocal(current, localImportStatements(current), plugins, loader)

          appendNewProgram(newProg)
          appendNewImports(newProg.imports, current, true)
          i += 1
        }else{
          // no more local imports
          // import a standard file
          val current = standardsToImport(j)
          val newProg = importStandard(current, standardImportStatements(current), plugins)

          appendNewProgram(newProg)
          appendNewImports(newProg.imports, current, false)
          j += 1
        }
      }
      PProgram(imports, macros, domains, fields, functions, predicates, methods, extensions, errors)(p.pos)
    }


    try {
      val program = RecParser(f).parses(s)
      val importedProgram = resolveImports(program)                             // Import programs
      val expandedProgram = MacroExpander.expandDefines(importedProgram)        // Expand macros
      expandedProgram
    }
    catch {
      case ParseException(msg, pos) =>
        val location = pos match {
          case (start: FilePosition, end: FilePosition) =>
            SourcePosition(start.file, start, end)
          case _ =>
            SourcePosition(_file, 0, 0)
        }
        PProgram(Nil, Nil, Nil, Nil, Nil, Nil, Nil, Nil, Seq(ParseError(msg, location)))((NoPosition, NoPosition))
    }
  }

  case class RecParser(file: Path) {

    def parses(s: String): PProgram = {
      _file = file.toAbsolutePath
      println(s"Parsing (${_file.toString()}):\n$s")

      // Add an empty line at the end to make `computeFrom(s.length)` return `(lines.length, 1)`, as the old
      // implementation of `computeFrom` used to do.
      val lines = s.linesWithSeparators
      _line_offset = (lines.map(_.length) ++ Seq(0)).toArray
      var offset = 0
      for (i <- _line_offset.indices) {
        val line_length = _line_offset(i)
        _line_offset(i) = offset
        offset += line_length
      }

      fastparse.parse(s, entireProgram(_)) match {
        case fastparse.Parsed.Success(prog, _) => prog
        case fail: fastparse.Parsed.Failure =>
          val trace = fail.trace()
          val fullStack = fastparse.Parsed.Failure.formatStack(trace.input, trace.stack)
          val msg = s"${trace.aggregateMsg}. Occurred while parsing: $fullStack"
          val (line, col) = lineCol.getPos(trace.index)
          val pos = FilePosition(_file, line, col)
          throw ParseException(msg, (pos, pos))
      }
    }
  }

  /**
    * Function that wraps a parser to provide start and end positions if the wrapped parser succeeds.
    */
  def FP[T](t: => P[T])(implicit ctx: P[_]): P[((FilePosition, FilePosition), T)] = {
    val startPos = lineCol.getPos(ctx.index)
    val res: P[T] = t
    val finishPos = lineCol.getPos(ctx.index)
    res.map({ parsed => ((FilePosition(_file, startPos._1, startPos._2), FilePosition(_file, finishPos._1, finishPos._2)), parsed) })
  }

  /**
    * Function that parses a file and converts it into a program
    *
    * @param buffer Buffer to read file from
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importProgram(imported_source: String, path: Path, importStmt: PImport, plugins: Option[SilverPluginManager]): PProgram = {

    val transformed_source = if (plugins.isDefined){
      plugins.get.beforeParse(imported_source, isImported = true) match {
        case Some(transformed) => transformed
        case None => throw ParseException(s"Plugin failed: ${plugins.get.errors.map(_.toString).mkString(", ")}", importStmt.pos)
      }
    } else {
      imported_source
    }
    RecParser(path).parses(transformed_source)
  }

  /**
    * Opens (and closes) standard file to be imported, parses it and converts it into a program.
    * Standard files are located in the resources inside a "import" folder.
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importStandard(path: Path, importStmt: PImport, plugins: Option[SilverPluginManager]): PProgram = {
    /* Prefix the standard library import (`path`) with the directory in which standard library
     * files are expected (`standard_import_directory`). The result is a OS-specific path, e.g.
     * "import\my\stdlib.vpr".
     */
    val relativeImportPath = Paths.get(standard_import_directory, path.toString)

    /* Creates a corresponding relative URL, e.g. "file://import/my/stdlib.vpr" */
    val relativeImportUrl = new URL(new URL("file:"), relativeImportPath.toString)

    /* Extract the path component only, e.g. "import/my/stdlib.vpr" */
    val relativeImportStr = relativeImportUrl.getPath

    // nested try-catch block because source.close() in finally could also cause a NullPointerException
    val buffer =
      try {
        /* Resolve the import using the specified class loader. Could point into the local file system
         * or into a jar file. The latter case requires `relativeImportStr` to be a valid URL (which
         * rules out Windows paths).
         */
        val source = scala.io.Source.fromResource(relativeImportStr, getClass.getClassLoader)

        try {
          source.getLines().toArray
        } catch {
          case e@(_: RuntimeException | _: java.io.IOException) =>
            throw ParseException(s"could not import file ($e)", importStmt.pos)
        } finally {
          source.close()
        }
      } catch {
        case _: java.lang.NullPointerException =>
          throw ParseException(s"""file <$path> does not exist""", importStmt.pos)
        case e@(_: RuntimeException | _: java.io.IOException) =>
          throw ParseException(s"could not import file ($e)", importStmt.pos)
      }
    val imported_source = buffer.mkString("\n") + "\n"
    importProgram(imported_source, path, importStmt, plugins)
  }

  /**
    * Opens (and closes) local file to be imported, parses it and converts it into a program.
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importLocal(path: Path, importStmt: PImport, plugins: Option[SilverPluginManager], loader: FileLoader): PProgram = {
    loader.loadContent(path) match {
      case Failure(exception) => throw ParseException(s"""could not import file ($exception)""", importStmt.pos)
      case Success(value) => importProgram(value, path, importStmt, plugins)
    }
  }

  lazy val keywords = FastParserCompanion.basicKeywords | ParserExtension.extendedKeywords

  import scala.language.implicitConversions
  implicit def LeadingWhitespaceStr(p: String)(implicit ctx: P[Any]): LeadingWhitespace[Unit] = new LeadingWhitespace(() => P(p))
  implicit def LeadingWhitespace[T](p: => P[T]) = new LeadingWhitespace(() => p)

  type Pos = (Position, Position)

  // Actual Parser starts from here
  def identStarts[$: P] = CharIn("A-Z", "a-z", "$_")
  def identContinues[$: P] = CharIn("0-9", "A-Z", "a-z", "$_")

  // def keywordLang[$: P](check: => P[_]): P[PKeywordLang] = P(FP(check.!).map { case (pos, k) => PKeywordLang(k)(pos) } ~~ !identContinues)./
  // def keywordStmt[$: P](check: => P[_]): P[PKeywordStmt] = P(FP(check.!).map { case (pos, k) => PKeywordStmt(k)(pos) } ~~ !identContinues)./
  // def keywordConst[$: P](check: => P[_]): P[PKeywordConstant] = P(FP(check.!).map { case (pos, k) => PKeywordConstant(k)(pos) } ~~ !identContinues)./
  // def keyword[$: P, T <: PKeyword](k: T): P[PKeyword2[T]] = P(FP(k.keyword).map { case (pos, ()) => PKeyword2(k)(pos) } ~~ !identContinues)./

  // def keywordOp[$: P](check: => P[_]): P[PKeywordOperator] = P(FP(check.!).map { case (pos, op) => PKeywordOperator(op)(pos) } ~~ !identContinues)./
  // def operator[$: P](check: => P[_], clashes: => Option[P[_]] = None): P[POperatorSymbol] = P(!clashes.getOrElse(Fail) ~~ FP(check.!).map { case (pos, op) => POperatorSymbol(op)(pos) })./
  // def wandOp[$: P]: P[PSymOp.Wand] = reserved(PSymOp.Wand)
  // def wandOp[$: P]: P[String] = StringIn(PKw.Domain.token).!

  def reservedKw[$: P, T <: PKeyword](r: T): P[PReserved[T]] = P(FP(r.token).map { case (pos, ()) => PReserved(r)(pos) } ~~ !identContinues)./
  def reservedSym[$: P, T <: PSymbol](r: T): P[PReserved[T]] = P(FP(r.token./).map { case (pos, ()) => PReserved(r)(pos) })
  def reservedSymMany[$: P, T <: PSymbol](clashes: => Option[P[_]], s: => P[_], f: String => T): P[PReserved[T]] =
    !clashes.getOrElse(Fail) ~~ FP(s.!./).map {
      case (pos, op) => PReserved(f(op))(pos)
    }
  /**
    * Parses one of many possible reserved words, should only be used with `StringIn` as `s`. The parser given in
    * `f` should be pre-initialized (e.g. from a `val`), see (here)[https://com-lihaoyi.github.io/fastparse/#FlatMap]. If only
    * a single reserved word is to be parsed, use `reservedKw` instead.
    */
  def reservedKwMany[$: P, U](s: => P[_], f: Pos => String => P[Pos => U]): P[U] =
    FP((FP(s.!) ~~ !identContinues)./.flatMap {
      case (pos, op) => f(pos)(op)
    }).map { case (pos, f) => f(pos) }

  // def reservedOperators[$: P, T <: PReservedString, U](s: => P[_], f: String => T): P[PReserved[T]] =
  //   FP((FP(s.!) ~~ !identContinues)./.flatMap {
  //     case (pos, op) => f(pos)(op)
  //   }).map { case (pos, f) => f(pos) }

  def parens[$: P, T](p: => P[T]) = "(" ~ p ~ ")"

  def angles[$: P, T](p: => P[T]) = "<" ~ p ~ ">"

  def quoted[$: P, T](p: => P[T]) = "\"" ~ p ~ "\""

  def block[$: P, T <: PNode](p: => P[T]): P[PBlock[T]] = FP("{" ~/ p ~ "}"./).map { case (pos, inner) => PBlock(inner)(pos) }

  def foldPExp[E <: PExp](e: E, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) => a(t) }

  def isFieldAccess(obj: Any) = {
    obj.isInstanceOf[PFieldAccess]
  }

  def atomReservedKw[$: P]: P[PExp] = reservedKwMany(
    StringIn("true", "false", "null", "old", "result", "acc", "none", "wildcard", "write", "epsilon", "perm", "let", "forall", "exists", "forperm",
      "unfolding", "applying", "Set", "Seq", "Multiset", "Map", "range", "domain", "new"),
    pos => _ match {
      case "true" => Pass.map(_ => PBoolLit(PReserved(PKw.True)(pos), true))
      case "false" => Pass.map(_ => PBoolLit(PReserved(PKw.False)(pos), false))
      case "null" => Pass.map(_ => PNullLit(PReserved(PKw.Null)(pos)))
      case "old" => old(PReserved(PKwOp.Old)(pos))
      case "result" => Pass.map(_ => PResultLit(PReserved(PKw.Result)(pos)))
      case "acc" => accessPredImpl(PReserved(PKwOp.Acc)(pos))
      case "none" => Pass.map(_ => PNoPerm(PReserved(PKw.None)(pos)))
      case "wildcard" => Pass.map(_ => PWildcard(PReserved(PKw.Wildcard)(pos)))
      case "write" => Pass.map(_ => PFullPerm(PReserved(PKw.Write)(pos)))
      case "epsilon" => Pass.map(_ => PEpsilon(PReserved(PKw.Epsilon)(pos)))
      case "perm" => perm(PReserved(PKwOp.Perm)(pos))
      case "let" => let(PReserved(PKwOp.Let)(pos))
      case "forall" => forall(PReserved(PKw.Forall)(pos))
      case "exists" => exists(PReserved(PKw.Exists)(pos))
      case "forperm" => forperm(PReserved(PKw.Forperm)(pos))
      case "unfolding" => unfolding(PReserved(PKwOp.Unfolding)(pos))
      case "applying" => applying(PReserved(PKwOp.Applying)(pos))
      case "Set" => setConstructor(PReserved(PKwOp.Set)(pos))
      case "Seq" => seqConstructor(PReserved(PKwOp.Seq)(pos))
      case "Multiset" => multisetConstructor(PReserved(PKwOp.Multiset)(pos))
      case "Map" => mapConstructor(PReserved(PKwOp.Map)(pos))
      case "range" => mapRange(PReserved(PKwOp.Range)(pos))
      case "domain" => mapDomain(PReserved(PKwOp.Domain)(pos))
      case "new" => newExp(PReserved(PKw.New)(pos))
    }
  )

  def atom(bracketed: Boolean = false)(implicit ctx : P[_]) : P[PExp] = P(ParserExtension.newExpAtStart(ctx) | annotatedAtom
    | atomReservedKw | integer | unExp | inhaleExhale | size | seqRange
    | maybeTypedFuncApp(bracketed) | idnuse | ParserExtension.newExpAtEnd(ctx))

  def atomParen[$: P](bracketed: Boolean = false): P[PExp] = P(parens(expParen(true)).map(e => { e.bracketed = true; e }) | atom(bracketed))

  def stringLiteral[$: P]: P[String] = P("\"" ~ CharsWhile(_ != '\"').! ~ "\"")

  def annotation[$: P]: P[PAnnotation] = FP(reservedSym(PSym.At) ~~ annotationIdentifier ~ parens(stringLiteral.rep(sep = ","./))).map {
    case (pos, (op, ident, args)) => PAnnotation(op, ident, args)(pos)
  }

  def annotated[$: P, T](inner: => P[PAnnotationsPosition => T]): P[T] = FP(annotation.rep(0) ~ inner).map {
    case (pos, (annotations, i)) => i(PAnnotationsPosition(annotations, pos))
  }

  def annotatedAtom[$: P]: P[PExp] = FP(annotation ~ atomParen()).map {
    case (pos, (ann, exp)) => PAnnotatedExp(ann, exp)(pos)
  }

  def result[$: P]: P[PResultLit] = reservedKw(PKw.Result).map(k => PResultLit(k)(k.pos))

  def unExp[$: P]: P[PUnExp] = FP((reservedSym(PSymOp.Minus) | reservedSym(PSymOp.Not)) ~ suffixExpr()).map { case (pos, (a, b)) => PUnExp(a, b)(pos) }

  def strInteger[$: P]: P[String] = P(CharIn("0-9").rep(1)).!

  def integer[$: P]: P[PIntLit] = FP(strInteger.filter(s => s.matches("\\S+"))).map { case (pos, s) => PIntLit(BigInt(s))(pos) }

  def identifier[$: P]: P[Unit] = identStarts ~~ identContinues.repX

  def annotationIdentifier[$: P]: P[PIdnRef] = FP((identStarts ~~ CharIn("0-9", "A-Z", "a-z", "$_.").repX).!).map {
    case (pos, id) => PIdnRef(id)(pos)
  }

  def ident[$: P]: P[String] = identifier.!.filter(a => !keywords.contains(a)).opaque("identifier")

  def idnuse[$: P]: P[PIdnUseExp] = FP(ident).map { case (pos, id) => PIdnUseExp(id)(pos) }

  def idnref[$: P]: P[PIdnRef] = FP(ident).map { case (pos, id) => PIdnRef(id)(pos) }

  def oldLabel[$: P]: P[PIdnUseExp] = idnuse | FP(LabelledOld.LhsOldLabel.!).map {
    case (pos, lhsOldLabel) => PIdnUseExp(lhsOldLabel)(pos)
  }

  def old[$: P](k: PReserved[PKwOp.Old.type]): P[Pos => POldExp] = P(("[" ~ oldLabel ~ "]").? ~ parens(exp)).map {
    case (a, b) => POldExp(k, a, b)
  }

  def magicWandExp[$: P](bracketed: Boolean = false): P[PExp] = FP(orExp(bracketed) ~~~ (reservedSym(PSymOp.Wand) ~ exp).lw.?).map {
    case (pos, (lhs, b)) => b match {
      case Some((op, rhs)) => PMagicWandExp(lhs, op, rhs)(pos)
      case None =>lhs
  }}

  def realMagicWandExp[$: P]: P[PMagicWandExp] = FP(orExp() ~ reservedSym(PSymOp.Wand) ~ exp).map {
    case (pos, (lhs, op, rhs)) => PMagicWandExp(lhs, op, rhs)(pos)
  }

  def implExp[$: P](bracketed: Boolean = false): P[PExp] = FP(magicWandExp(bracketed) ~~~ (reservedSym(PSymOp.Implies) ~ implExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def iffExp[$: P](bracketed: Boolean = false): P[PExp] = FP(implExp(bracketed) ~~~ (reservedSym(PSymOp.Iff) ~ iffExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some((op, c)) => PBinExp(a, op, c)(pos)
      case None => a
    }
  }

  def iteExpr[$: P](bracketed: Boolean = false): P[PExp] = FP(iffExp(bracketed) ~~~ (reservedSym(PSymOp.Question) ~ iteExpr() ~ reservedSym(PSymOp.Colon) ~ iteExpr()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some((q, thn, c, els)) => PCondExp(a, q, thn, c, els)(pos)
      case None => a
    }
  }

  def expParen[$: P](bracketed: Boolean): P[PExp] = P(iteExpr(bracketed))

  def exp[$: P]: P[PExp] = P(expParen(false))

  def indexSuffix[$: P]: P[(PReserved[PSymOp.LBracket.type], PExp, PReserved[PSymOp.RBracket.type], Pos) => SuffixedExpressionGenerator[PExp]] = P(
    (reservedSym(PSymOp.Assign) ~ exp).map { case (a, v) => (l: PReserved[PSymOp.LBracket.type], i: PExp, r: PReserved[PSymOp.RBracket.type], pos: Pos)
      => SuffixedExpressionGenerator[PExp](e => PUpdate(e, l, i, a, v, r)(e.pos._1, pos._2)) } |
    // Need to have `".." ~ exp` before `".." ~ Pass` and both of those before `Pass` to avoid issues due to some implicit cut when `indexSuffix` succeeds
    (reservedSym(PSymOp.DotDot) ~ exp.?).map { case (d, m) => (l: PReserved[PSymOp.LBracket.type], n: PExp, r: PReserved[PSymOp.RBracket.type], pos: Pos)
      => SuffixedExpressionGenerator[PExp](e => PSeqSlice(e, l, Some(n), d, m, r)(e.pos._1, pos._2)) } |
    Pass.map(_ => (l: PReserved[PSymOp.LBracket.type], e1: PExp, r: PReserved[PSymOp.RBracket.type], pos: Pos)
      => SuffixedExpressionGenerator[PExp](e0 => PLookup(e0, l, e1, r)(e0.pos._1, pos._2))))

  def suffix[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(FP((!".." ~~ reservedSym(PSymOp.Dot)) ~ idnref).map { case (pos, (dot, id)) => SuffixedExpressionGenerator[PExp](e => PFieldAccess(e, dot, id)(e.pos._1, pos._2)) } |
      FP(reservedSym(PSymOp.LBracket) ~ (
        (reservedSym(PSymOp.DotDot) ~ exp).map { case (d, n) => (l: PReserved[PSymOp.LBracket.type], r: PReserved[PSymOp.RBracket.type], pos: Pos)
          => SuffixedExpressionGenerator[PExp](e => PSeqSlice(e, l, None, d, Some(n), r)(e.pos._1, pos._2)) }
      | (exp ~ indexSuffix).map { case (e, s) => (l: PReserved[PSymOp.LBracket.type], r: PReserved[PSymOp.RBracket.type], pos: Pos)
          => s(l, e, r, pos) }
      ) ~ reservedSym(PSymOp.RBracket)).map { case (pos, (l, f, r)) => f(l, r, pos) })

  def suffixExpr[$: P](bracketed: Boolean = false): P[PExp] = P((atomParen(bracketed) ~~~ suffix.lw.rep).map { case (fac, ss) => foldPExp(fac, ss) })

  def termOp[$: P] = P(reservedSymMany(None, StringIn("*", "/", "\\", "%"), _ match {
    case "*" => PSymOp.Mul
    case "/" => PSymOp.Div
    case "\\" => PSymOp.ArithDiv
    case "%" => PSymOp.Mod
  }))

  def term[$: P](bracketed: Boolean = false): P[PExp] = P((suffixExpr(bracketed) ~~~ termd.lw.rep).map { case (a, ss) => foldPExp(a, ss) })

  def termd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = FP(termOp ~/ suffixExpr()).map { case (pos, (op, id)) => SuffixedExpressionGenerator(e => PBinExp(e, op, id)(e.pos._1, pos._2)) }

  def sumOp[$: P]: P[PReserved[PBinaryOp]] = P(reservedSymMany(Some("--*"), StringIn("++", "+", "-"), _ match {
    case "++" => PSymOp.Append
    case "+" => PSymOp.Plus
    case "-" => PSymOp.Minus
  }) | reservedKwMany(StringIn("union", "intersection", "setminus", "subset"), _ => _ match {
    case "union" => Pass.map(_ => PReserved(PKwOp.Union))
    case "intersection" => Pass.map(_ => PReserved(PKwOp.Intersection))
    case "setminus" => Pass.map(_ => PReserved(PKwOp.Setminus))
    case "subset" => Pass.map(_ => PReserved(PKwOp.Subset))
  }))

  def sum[$: P](bracketed: Boolean = false): P[PExp] = P((term(bracketed) ~~~ sumd.lw.rep).map { case (a, ss) => foldPExp(a, ss) })

  def sumd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = FP(sumOp ~/ term()).map { case (pos, (op, id)) => SuffixedExpressionGenerator(e => PBinExp(e, op, id)(e.pos._1, pos._2)) }

  def cmpOp[$: P]: P[PReserved[PBinaryOp]] = P(reservedSymMany(Some("<==>"), StringIn("<=", ">=", "<", ">"), _ match {
    case "<=" => PSymOp.Le
    case ">=" => PSymOp.Ge
    case "<" => PSymOp.Lt
    case ">" => PSymOp.Gt
  }) | reservedKw(PKwOp.In))

  val cmpOps = Set("<=", ">=", "<", ">", "in")

  def cmpd[$: P]: P[PExp => SuffixedExpressionGenerator[PBinExp]] = FP(cmpOp ~/ sum()).map {
    case (pos, (op, right)) => chainComp(op, right, pos)
  }

  def chainComp(op: PReserved[PBinaryOp], right: PExp, pos: (FilePosition, FilePosition))(from: PExp) = SuffixedExpressionGenerator(_ match {
      case left@PBinExp(_, op0, middle) if cmpOps.contains(op0.rs.token) && left != from =>
        PBinExp(left, PReserved(PSymOp.AndAnd)(NoPosition, NoPosition), PBinExp(middle, op, right)(middle.pos._1, pos._2))(left.pos._1, pos._2)
      case left@PBinExp(_, PReserved(PSymOp.AndAnd), PBinExp(_, op0, middle)) if cmpOps.contains(op0.rs.token) && left != from =>
        PBinExp(left, PReserved(PSymOp.AndAnd)(NoPosition, NoPosition), PBinExp(middle, op, right)(middle.pos._1, pos._2))(left.pos._1, pos._2)
      case left => PBinExp(left, op, right)(left.pos._1, pos._2)
  })

  def cmpExp[$: P](bracketed: Boolean = false): P[PExp] = P((sum(bracketed) ~~~ cmpd.lw.rep).map {
    case (from, others) => foldPExp(from, others.map(_(from)))
  })

  def eqOp[$: P] = P(reservedSymMany(Some("==>"), StringIn("==", "!="), _ match {
    case "==" => PSymOp.EqEq
    case "!=" => PSymOp.Ne
  }))

  def eqExpParen[$: P](bracketed: Boolean = false): P[PExp] = FP(cmpExp(bracketed) ~~~ (eqOp ~/ eqExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }
  def eqExp[$: P]: P[PExp] = eqExpParen()

  def andExp[$: P](bracketed: Boolean = false): P[PExp] = FP(eqExpParen(bracketed) ~~~ (reservedSym(PSymOp.AndAnd) ~ andExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def orExp[$: P](bracketed: Boolean = false): P[PExp] = FP(andExp(bracketed) ~~~ (reservedSym(PSymOp.OrOr) ~ orExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def accessPredImpl[$: P](k: PReserved[PKwOp.Acc.type]): P[Pos => PAccPred] = P("(" ~ locAcc ~ ("," ~/ exp).? ~ ")").map {
    case (loc, perms) => {
      PAccPred(k, loc, perms.getOrElse(PFullPerm.implied()))
    }
  }

  def accessPred[$: P]: P[PAccPred] = FP(reservedKw(PKwOp.Acc).flatMap(accessPredImpl(_))).map { case (pos, f) => f(pos) }

  def resAcc[$: P]: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  def locAcc[$: P]: P[PLocationAccess] = P(fieldAcc | predAcc)

  def fieldAcc[$: P]: P[PFieldAccess] =
    P(NoCut(suffixExpr().filter(isFieldAccess)).map {
      case fa: PFieldAccess => fa
      case other => sys.error(s"Unexpectedly found $other")
    })

  def predAcc[$: P]: P[PCall] = funcApp

  def actualArgList[$: P]: P[Seq[PExp]] = exp.rep(sep = ","./)

  def inhaleExhale[$: P]: P[PExp] = FP(reservedSym(PSymOp.LBracket) ~ NoCut(exp) ~ reservedSym(PSymOp.Comma) ~ exp ~ reservedSym(PSymOp.RBracket)).map {
    case (pos, (l, a, c, b, r)) => PInhaleExhaleExp(l, a, c, b, r)(pos)
  }

  def perm[$: P](k: PReserved[PKwOp.Perm.type]): P[Pos => PCurPerm] = P(parens(resAcc)).map{ case r => PCurPerm(k, r) }

  def let[$: P](k: PReserved[PKwOp.Let.type]): P[Pos => PExp] =
    P(idndef ~ reservedSym(PSymOp.EqEq) ~ "(" ~ exp ~ ")" ~ reservedKw(PKwOp.In) ~ exp).map {
      case (id, eq, exp1, in, exp2) =>
        exp1.bracketed = true
        val nestedScope = PLetNestedScope(exp2)(exp2.pos)
        /* Type unresolvedType is expected to be replaced with the type of exp1
        * after the latter has been resolved
        * */
        val logicalVar = PLogicalVarDecl(id, PUnknown()())(id.pos)
        pos => {
          val let = PLet(k, logicalVar, eq, exp1, in, nestedScope)(pos)
          nestedScope.outerLet = let
          let
        }
    }

  def idndef[$: P]: P[PIdnDef] = FP(ident).map {
    case (pos, s) =>
      PIdnDef(s)(pos)
    }

  def forall[$: P](k: PReserved[PKw.Forall.type]): P[Pos => PExp] = P(nonEmptyIdnTypeList ~ reservedSym(PSym.ColonColon) ~ trigger.rep ~ exp).map {
    case (a, o, b, c) =>
      PForall(k, a.map(PLogicalVarDecl(_)), o, b, c)
    }
  def exists[$: P](k: PReserved[PKw.Exists.type]): P[Pos => PExp] = P(nonEmptyIdnTypeList ~ reservedSym(PSym.ColonColon) ~ trigger.rep ~ exp).map {
    case (a, o, b, c) =>
      PExists(k, a.map(PLogicalVarDecl(_)), o, b, c)
    }

  def nonEmptyIdnTypeList[$: P]: P[Seq[PIdnTypeBinding]] = P(idnTypeBinding.rep(min = 1, sep = ","./))

  def idnTypeBinding[$: P]: P[PIdnTypeBinding] = FP(idndef ~ ":" ~/ typ).map { case (pos, (a, b)) => PIdnTypeBinding(a, b)(pos) }

  def typReservedKw[$: P]: P[PType] = reservedKwMany(
    StringIn("Rational", "Int", "Bool", "Perm", "Ref", "Seq", "Set", "Multiset", "Map"),
    pos => _ match {
      case "Rational" => Pass.map { _ =>
          val p = pos.asInstanceOf[(HasLineColumn, HasLineColumn)]
          _warnings = _warnings :+ ParseWarning("Rational is deprecated, use Perm instead", SourcePosition(_file, p._1, p._2))
          PPrimitiv(PReserved(PKw.Perm)(pos))
        }
      case "Int" => Pass.map(_ => PPrimitiv(PReserved(PKw.Int)(pos)))
      case "Bool" => Pass.map(_ => PPrimitiv(PReserved(PKw.Bool)(pos)))
      case "Perm" => Pass.map(_ => PPrimitiv(PReserved(PKw.Perm)(pos)))
      case "Ref" => Pass.map(_ => PPrimitiv(PReserved(PKw.Ref)(pos)))
      case "Seq" => seqType(PReserved(PKw.Seq)(pos))
      case "Set" => setType(PReserved(PKw.Set)(pos))
      case "Multiset" => multisetType(PReserved(PKw.Multiset)(pos))
      case "Map" => mapType(PReserved(PKw.Map)(pos))
    }
  )

  def typ[$: P]: P[PType] = P(typReservedKw | domainTyp | macroType)

  def domainTyp[$: P]: P[PDomainType] = FP(idnref ~~~ ("[" ~ typ.rep(sep = ","./) ~ "]").lw.?).map {
    // domain type optionally without type arguments (might also be a type variable)
    case (pos, (a, b)) => PDomainType(a, b.toSeq.flatten)(pos)
  }

  def seqType[$: P](k: PReserved[PKw.Seq.type]): P[Pos => PSeqType] = P("[" ~ typ ~ "]").map{ case t => PSeqType(k, t) }

  def setType[$: P](k: PReserved[PKw.Set.type]): P[Pos => PSetType] = P("[" ~ typ ~ "]").map{ case t => PSetType(k, t) }

  def multisetType[$: P](k: PReserved[PKw.Multiset.type]): P[Pos => PMultisetType] = P("[" ~ typ ~ "]").map{ case t => PMultisetType(k, t) }

  def mapType[$: P](k: PReserved[PKw.Map.type]): P[Pos => PMapType] = P("[" ~ typ ~ "," ~ typ ~ "]").map {
   case (keyType, valueType) => PMapType(k, keyType, valueType)
  }

  /** Only for call-like macros, `idnuse`-like ones are parsed by `domainTyp`. */
  def macroType[$: P] : P[PMacroType] = funcApp.map(PMacroType(_))

  def trigger[$: P]: P[PTrigger] = FP("{" ~/ exp.rep(sep = ","./) ~ "}"./).map{
    case (pos, s) => PTrigger(s)(pos)
  }

  def forperm[$: P](k: PReserved[PKw.Forperm.type]): P[Pos => PExp] = P(nonEmptyIdnTypeList ~ "[" ~ resAcc ~ "]" ~ reservedSym(PSym.ColonColon) ~ exp).map {
    case (args, res, op, body) => PForPerm(k, args.map(PLogicalVarDecl(_)), res, op, body)
  }

  def unfolding[$: P](k: PReserved[PKwOp.Unfolding.type]): P[Pos => PExp] = P(predicateAccessPred ~ reservedKw(PKwOp.In) ~ exp).map {
    case (a, in, b) => PUnfolding(k, a, in, b)
  }

  def applying[$: P](k: PReserved[PKwOp.Applying.type]): P[Pos => PExp] = P("(" ~ magicWandExp() ~ ")" ~ reservedKw(PKwOp.In) ~ exp).map {
    case (a, op, b) =>
      a.bracketed = true
      PApplying(k, a, op, b)
  }

  def predicateAccessPred[$: P]: P[PAccPred] = P(accessPred | FP(predAcc).map {
    case (pos, loc) => PAccPred(PReserved(PKwOp.Acc)(NoPosition, NoPosition), loc, PFullPerm.implied())(pos)
  })

  def setConstructor[$: P](k: PReserved[PKwOp.Set.type]): P[Pos => PExp] = builtinConstructor(typ, exp)(t => PEmptySet(k, t.getOrElse(PTypeVar("#E"))), v => PExplicitSet(k, v))

  def seqConstructor[$: P](k: PReserved[PKwOp.Seq.type]): P[Pos => PExp] = builtinConstructor(typ, exp)(t => PEmptySeq(k, t.getOrElse(PTypeVar("#E"))), v => PExplicitSeq(k, v))

  def multisetConstructor[$: P](k: PReserved[PKwOp.Multiset.type]): P[Pos => PExp] = builtinConstructor(typ, exp)(t => PEmptyMultiset(k, t.getOrElse(PTypeVar("#E"))), v => PExplicitMultiset(k, v))

  def mapConstructor[$: P](k: PReserved[PKwOp.Map.type]): P[Pos => PExp] = builtinConstructor(typ ~ "," ~ typ, maplet)(t => PEmptyMap(k, t.map(_._1).getOrElse(PTypeVar("#K")), t.map(_._2).getOrElse(PTypeVar("#E"))), v => PExplicitMap(k, v))

  def builtinConstructor[$: P, T, E](types: => P[T], element: => P[E])(empty: Option[T] => Pos => PExp, nonEmpty: Seq[E] => Pos => PExp): P[Pos => PExp] =
    P((("[" ~ types ~ "]").? ~ "(" ~ ")").map(empty) | ("(" ~ element.rep(sep = ","./, min = 1) ~ ")").map(nonEmpty))

  def size[$: P]: P[PExp] = P(FP("|" ~/ exp ~ "|"./).map {
    case (pos, e) => PSize(e)(pos)
  })

  def seqRange[$: P]: P[PExp] = FP(reservedSym(PSymOp.LBracket) ~ NoCut(exp) ~ reservedSym(PSymOp.DotDot) ~ exp ~ reservedSym(PSymOp.RParen)).map { case (pos, (l, a, d, b, r)) => PRangeSeq(l, a, d, b, r)(pos) }

  def maplet[$: P]: P[PMaplet] = P(FP(exp ~ ":=" ~/ exp).map {
    case (pos, (key, value)) => PMaplet(key, value)(pos)
  })

  def mapDomain[$: P](k: PReserved[PKwOp.Domain.type]): P[Pos => PMapDomain] = P("(" ~ exp ~ ")").map {
    case e => PMapDomain(k, e)
  }

  def mapRange[$: P](k: PReserved[PKwOp.Range.type]): P[Pos => PMapRange] = P("(" ~ exp ~ ")").map {
    case e => PMapRange(k, e)
  }

  def newExp[$: P](k: PReserved[PKw.New.type]): P[Pos => PNewExp] = P("(" ~ newExpFields ~ ")").map { case fields => PNewExp(k, fields) }

  def newExpFields[$: P]: P[Option[Seq[PIdnUseExp]]] = P(P("*").map(_ => None) | P(idnuse.rep(sep = ","./)).map(Some(_)))

  def funcApp[$: P]: P[PCall] = FP(idnref ~ parens(actualArgList)).map {
    case (pos, (func, args)) =>
      PCall(func, args, None)(pos)
  }

  def maybeTypedFuncApp[$: P](bracketed: Boolean): P[PCall] = P(if (!bracketed) funcApp else FP(funcApp ~~~ (":" ~/ typ).lw.?).map {
    case (pos, (func, typeGiven)) => func.copy(typeAnnotated = typeGiven)(pos)
  })

  def stmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | annotatedStmt |
    fold | unfold | exhale | assertStmt |
    inhale | assume | ifThenElse | whileStmt | localVars | defineDeclStmt |
    goto | label | packageWand | applyWand | stmtBlock |
    quasihavoc | quasihavocall | assign | methodCall | ParserExtension.newStmtAtEnd(ctx))

  def annotatedStmt(implicit ctx : P[_]): P[PStmt] = (FP(annotation ~ stmt).map{
    case (pos, (ann, pStmt)) => PAnnotatedStmt(ann, pStmt)(pos)
  })

  def nodefinestmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | annotatedStmt |
    fold | unfold | exhale | assertStmt |
    inhale | assume | ifThenElse | whileStmt | localVars |
    goto | label | packageWand | applyWand | stmtBlock |
    quasihavoc | quasihavocall | assign | methodCall | ParserExtension.newStmtAtEnd(ctx))

  def assignTarget[$: P]: P[PAssignTarget] = P(fieldAcc | NoCut(funcApp) | idnuse)

  def assign[$: P]: P[PAssign] = FP(assignTarget.rep(min = 1, sep = ","./) ~ reservedSym(PSymOp.Assign) ~ exp).map { case (pos, (targets, op, rhs)) => PAssign(targets, Some(op), rhs)(pos) }

  def methodCall[$: P]: P[PAssign] = FP(funcApp | idnuse).map { case (pos, rhs) => PAssign(Nil, None, rhs)(pos) }

  def fold[$: P]: P[PFold] = FP(reservedKw(PKw.Fold) ~ predicateAccessPred).map{ case (pos, (k, e)) => PFold(k, e)(pos)}

  def unfold[$: P]: P[PUnfold] = FP(reservedKw(PKw.Unfold) ~ predicateAccessPred).map{ case (pos, (k, e)) => PUnfold(k, e)(pos)}

  def exhale[$: P]: P[PExhale] = FP(reservedKw(PKw.Exhale) ~ exp).map{ case (pos, (k, e)) => PExhale(k, e)(pos) }

  def assertStmt[$: P]: P[PAssert] = FP(reservedKw(PKw.Assert) ~ exp).map{ case (pos, (k, e)) => PAssert(k, e)(pos) }

  def inhale[$: P]: P[PInhale] = FP(reservedKw(PKw.Inhale) ~ exp).map{ case (pos, (k, e)) => PInhale(k, e)(pos) }

  def assume[$: P]: P[PAssume] = FP(reservedKw(PKw.Assume) ~ exp).map{ case (pos, (k, e)) => PAssume(k, e)(pos) }

  // Parsing Havoc statements
  // Havoc statements have two forms:
  // in the grammar. Note that it is still possible to express "(<exp1> ==> <exp2>) ==> <resource>
  // using parentheses.

  // Havocall follows a similar pattern to havoc but allows quantifying over variables.

  def quasihavoc[$: P]: P[PQuasihavoc] = FP(reservedKw(PKw.Quasihavoc) ~
    (NoCut(magicWandExp()) ~ reservedSym(PSymOp.Implies)).? ~ exp ).map {
      case (pos, (k, lhs, rhs)) => PQuasihavoc(k, lhs, rhs)(pos)
  }

  def quasihavocall[$: P]: P[PQuasihavocall] = FP(reservedKw(PKw.Quasihavocall) ~
    nonEmptyIdnTypeList ~ reservedSym(PSym.ColonColon) ~ (NoCut(magicWandExp()) ~ reservedSym(PSymOp.Implies)).? ~ exp).map {
    case (pos, (k, vars, c, lhs, rhs)) => PQuasihavocall(k, vars.map(PLogicalVarDecl(_)), c, lhs, rhs)(pos)
  }

  def ifThenElse[$: P]: P[PIf] = FP(reservedKw(PKw.If) ~ "(" ~ exp ~ ")" ~ stmtBlock ~~~ elseIfOrElse).map {
    case (pos, (k, cond, thn, (eleKw, ele))) => PIf(k, cond, thn, eleKw, ele)(pos)
  }

  def stmtBlock[$: P]: P[PSeqn] =  FP("{" ~ (stmt ~/ ";".?).rep ~ "}").map{ case (pos, e) => PSeqn(e)(pos)}

  def elseIfOrElse[$: P]: LW[(Option[PReserved[PKw.Else.type]], PSeqn)] = elseIf.lw | elseBlock

  def elseIf[$: P]: P[(Option[PReserved[PKw.Else.type]], PSeqn)] = FP(reservedKw(PKw.Elseif) ~ "(" ~ exp ~ ")" ~ stmtBlock ~~~ elseIfOrElse).map {
    case (pos, (k, cond, thn, (eleKw, ele))) => (None, PSeqn(Seq(PIf(k, cond, thn, eleKw, ele)(pos)))(pos))
  }

  def elseBlock[$: P]: LW[(Option[PReserved[PKw.Else.type]], PSeqn)] = (
    (reservedKw(PKw.Else) ~/ stmtBlock).map(p => (Some(p._1), p._2)) |
    FP(Pass).map { case (pos, _) => (None, PSeqn(Nil)(pos)) }
  ).lw

  def whileStmt[$: P]: P[PWhile] = FP(reservedKw(PKw.While) ~ "(" ~ exp ~ ")" ~ invariant.rep ~ stmtBlock).map {
    case (pos, (k, cond, invs, body)) =>
      PWhile(k, cond, invs, body)(pos)
  }

  def invariant(implicit ctx : P[_]) : P[(PReserved[PSpecification], PExp)] = P((reservedKw(PKw.Invariant) ~ exp ~~~ ";".lw.?) | ParserExtension.invSpecification(ctx))

  def localVars[$: P]: P[PVars] = FP(reservedKw(PKw.Var) ~ nonEmptyIdnTypeList ~~~ (reservedSym(PSymOp.Assign) ~ exp).lw.?).map {
    case (pos, (k, a, b)) => PVars(k, a.map(PLocalVarDecl(_)), b)(pos)
  }

  def defineDecl[$: P]: P[PAnnotationsPosition => PDefine] = P(reservedKw(PKw.Define) ~ idndef ~ ("(" ~ idndef.rep(sep = ","./) ~ ")").? ~ (
    FP("{" ~/ (nodefinestmt ~ ";".?).rep ~ "}"./).map { case (pos, c) => (k: PReserved[PKw.Define.type], a: PIdnDef, b: Option[Seq[PIdnDef]]) => ap: PAnnotationsPosition => PDefine(ap.annotations, k, a, b, PSeqn(c)(pos))(ap.pos) } |
    exp.map(e => (k: PReserved[PKw.Define.type], a: PIdnDef, b: Option[Seq[PIdnDef]]) => (ap: PAnnotationsPosition) => PDefine(ap.annotations, k, a, b, e)(ap.pos)))).map {
      case (k, a, b, c) => c(k, a, b)
  }
  def defineDeclStmt[$: P]: P[PDefine] = FP(defineDecl).map { case (pos, e) => e(PAnnotationsPosition(Nil, pos)) }

  def goto[$: P]: P[PGoto] = FP(reservedKw(PKw.Goto) ~ idnuse).map{ case (pos, (k, e)) => PGoto(k, e)(pos) }

  def label[$: P]: P[PLabel] = FP(reservedKw(PKw.Label) ~/ idndef ~~~ (reservedKw(PKw.Invariant) ~/ exp).lw.rep).map {
    case (pos, (k, name, invs)) => PLabel(k, name, invs)(pos) }

  def packageWand[$: P]: P[PPackageWand] = FP(reservedKw(PKw.Package) ~ magicWandExp() ~~~ stmtBlock.lw.?).map {
    case (pos, (k, wand, Some(proofScript))) =>
      PPackageWand(k, wand, proofScript)(pos)
    case (pos, (k, wand, None)) =>
      PPackageWand(k, wand, PSeqn(Seq())(pos))(pos)
  }

  def applyWand[$: P]: P[PApplyWand] = FP(reservedKw(PKw.Apply) ~ magicWandExp()).map {
    case (pos, (k, p)) => PApplyWand(k, p)(pos)
  }

  def programMember(implicit ctx : P[_]): P[PNode] = annotated(ParserExtension.newDeclAtStart(ctx) | preambleImport | defineDecl | fieldDecl | methodDecl | domainDecl | functionDecl | predicateDecl | ParserExtension.newDeclAtEnd(ctx))

  def programDecl[$: P]: P[PProgram] =
    FP(programMember.rep).map {
    case (pos, decls) => {
      val warnings = _warnings
      _warnings = Seq()
      PProgram(
        decls.collect { case i: PImport => i }, // Imports
        decls.collect { case d: PDefine => d }, // Macros
        decls.collect { case d: PDomain => d }, // Domains
        decls.collect { case f: PFields => f }, // Fields
        decls.collect { case f: PFunction => f }, // Functions
        decls.collect { case p: PPredicate => p }, // Predicates
        decls.collect { case m: PMethod => m }, // Methods
        decls.collect { case e: PExtender => e }, // Extensions
        warnings // Parse Warnings
      )(pos)
    }
  }

  def preambleImport[$: P]: P[PAnnotationsPosition => PImport] = P(reservedKw(PKw.Import) ~
    (FP(quoted(relativeFilePath)).map { case (pos, s) => (true, PStringLiteral(s)(pos)) }
   | FP(angles(relativeFilePath)).map { case (pos, s) => (false, PStringLiteral(s)(pos)) })
  ).map {
    case (k, (local, filename)) => ap: PAnnotationsPosition => PImport(ap.annotations, k, local, filename)(ap.pos)
  }

  def relativeFilePath[$: P]: P[String] = (CharIn("~.").? ~~ (CharIn("/").? ~~ CharIn(".", "A-Z", "a-z", "0-9", "_\\- \n\t")).rep(1)).!

  def anyString[$: P]: P[String] = P(CharPred(c => c !='\"').rep(1).!)

  def domainDecl[$: P]: P[PAnnotationsPosition => PDomain] = P(reservedKw(PKw.Domain) ~ idndef ~ typeParams ~ (reservedKw(PKw.Interpretation) ~ parens((ident ~ ":" ~ quoted(anyString.!)).rep(sep = ","))).? ~
    block(FP(annotated(domainFunctionDecl | axiomDecl).rep).map(ms => PDomainMembers1(ms._2)(ms._1)))).map {
    case (k, name, typparams, interpretations, block) =>
      val members = block.inner.members
      val funcs1 = members collect { case m: PDomainFunction1 => m }
      val axioms1 = members collect { case m: PAxiom1 => m }
      val funcs = funcs1 map (f => PDomainFunction(f.annotations, f.unique, f.function, f.idndef, f.formalArgs, f.typ, f.interpretation)(PIdnRef(name.name)(name.pos))(f.pos))
      val axioms = axioms1 map (a => PAxiom(a.annotations, a.axiom, a.idndef, a.exp)(PIdnRef(name.name)(name.pos))(a.pos))
      ap: PAnnotationsPosition => PDomain(
        ap.annotations,
        k,
        name,
        typparams,
        PDomainMembers(funcs, axioms)(block.pos),
        interpretations.map(i => (i._1, i._2.toMap)))(ap.pos)
  }

  def domainTypeVarDecl[$: P]: P[PTypeVarDecl] = FP(idndef).map{ case (pos, i) => PTypeVarDecl(i)(pos) }

  def typeParams[$: P]: P[Seq[PTypeVarDecl]] = P(("[" ~ domainTypeVarDecl.rep(sep = ","./) ~ "]").?).map(_.getOrElse(Nil))

  def domainFunctionDecl[$: P]: P[PAnnotationsPosition => PDomainFunction1] = P(reservedKw(PKw.Unique).? ~ domainFunctionSignature ~ (reservedKw(PKw.Interpretation) ~ quoted(anyString.!)).? ~~~ ";".lw.?).map {
    case (unique, fdecl, interpretation) => fdecl match {
      case (function, name, formalArgs, t) => ap: PAnnotationsPosition => PDomainFunction1(ap.annotations, unique, function, name, formalArgs, t, interpretation)(ap.pos)
    }
  }

  def domainFunctionSignature[$: P] = P(reservedKw(PKw.Function) ~ idndef ~ "(" ~ anyFormalArgList ~ ")" ~ ":" ~ typ)

  def anyFormalArgList[$: P]: P[Seq[PAnyFormalArgDecl]] = P((formalArg | unnamedFormalArg).rep(sep = ","./))

  def formalArg[$: P]: P[PFormalArgDecl] = P(idnTypeBinding.map(PFormalArgDecl(_)))

  def unnamedFormalArg[$: P] = FP(typ).map{ case (pos, t) => PUnnamedFormalArgDecl(t)(pos) }

  def formalArgList[$: P]: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","./))

  def formalReturnList[$: P]: P[Seq[PFormalReturnDecl]] = P(idnTypeBinding.map(PFormalReturnDecl(_)).rep(sep = ","./))

  def axiomDecl[$: P]: P[PAnnotationsPosition => PAxiom1] = P(reservedKw(PKw.Axiom) ~ idndef.? ~ block(exp) ~~~ ";".lw.?).map { case (k, a, b) =>
    ap: PAnnotationsPosition => PAxiom1(ap.annotations, k, a, b)(ap.pos)
  }

  def fieldDecl[$: P]: P[PAnnotationsPosition => PFields] = P(reservedKw(PKw.Field) ~ nonEmptyIdnTypeList ~~~ ";".lw.?).map {
    case (k, a) => ap: PAnnotationsPosition => PFields(ap.annotations, k, a.map(PFieldDecl(_)))(ap.pos)
  }

  def functionDecl[$: P]: P[PAnnotationsPosition => PFunction] = P(reservedKw(PKw.Function) ~ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~~~ precondition.lw.rep ~~~
    postcondition.lw.rep ~~~ block(exp).lw.?).map({ case (k, a, b, c, d, e, f) =>
      ap: PAnnotationsPosition => PFunction(ap.annotations, k, a, b, c, d, e, f)(ap.pos)
  })


  def precondition(implicit ctx : P[_]) : P[(PReserved[PSpecification], PExp)] = P((reservedKw(PKw.Requires) ~ exp ~~~ ";".lw.?) | ParserExtension.preSpecification(ctx))

  def postcondition(implicit ctx : P[_]) : P[(PReserved[PSpecification], PExp)] = P((reservedKw(PKw.Ensures) ~ exp ~~~ ";".lw.?) | ParserExtension.postSpecification(ctx))

  def predicateDecl[$: P]: P[PAnnotationsPosition => PPredicate] = P(reservedKw(PKw.Predicate) ~ idndef ~ "(" ~ formalArgList ~ ")" ~~~ (block(exp)).lw.?).map {
    case (k, a, b, c) =>
      ap: PAnnotationsPosition => PPredicate(ap.annotations, k, a, b, c)(ap.pos)
  }

  def methodDecl[$: P]: P[PAnnotationsPosition => PMethod] = P(methodSignature ~~~/ precondition.lw.rep ~~~ postcondition.lw.rep ~~~ stmtBlock.lw.?).map {
    case (k, name, args, rets, pres, posts, body) =>
      ap: PAnnotationsPosition => PMethod(ap.annotations, k, name, args, rets.map(_._1), rets.map(_._2).getOrElse(Nil), pres, posts, body)(ap.pos)
  }

  def methodSignature[$: P] = P(reservedKw(PKw.Method) ~ idndef ~ "(" ~ formalArgList ~ ")" ~~~ (reservedKw(PKw.Returns) ~ "(" ~ formalReturnList ~ ")").lw.?)

  def entireProgram[$: P]: P[PProgram] = P(Start ~ programDecl ~ End)


  object ParserExtension extends ParserPluginTemplate {

    import ParserPluginTemplate._

    /**
      * These private variables are the storage variables for each of the extensions.
      * As the parser are evaluated lazily, it is possible for us to stores extra parsing sequences in these variables
      * and after the plugins are loaded, the parsers are added to these variables and when any parser is required,
      * can be referenced back.
      */
    private var _newDeclAtEnd: Option[Extension[PAnnotationsPosition => PExtender]] = None
    private var _newDeclAtStart: Option[Extension[PAnnotationsPosition => PExtender]] = None

    private var _newExpAtEnd: Option[Extension[PExp]] = None
    private var _newExpAtStart: Option[Extension[PExp]] = None

    private var _newStmtAtEnd: Option[Extension[PStmt]] = None
    private var _newStmtAtStart: Option[Extension[PStmt]] = None

    private var _preSpecification: Option[Extension[(PReserved[PSpecification], PExp)]] = None
    private var _postSpecification: Option[Extension[(PReserved[PSpecification], PExp)]] = None
    private var _invSpecification: Option[Extension[(PReserved[PSpecification], PExp)]] = None

    private var _extendedKeywords: Set[String] = Set()


    /**
      * For more details regarding the functionality of each of these initial parser extensions
      * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
      */
    override def newDeclAtStart : Extension[PAnnotationsPosition => PExtender] = _newDeclAtStart match {
      case None => super.newDeclAtStart
      case Some(ext) => ext
    }

    override def newDeclAtEnd : Extension[PAnnotationsPosition => PExtender] = _newDeclAtEnd match {
      case None => super.newDeclAtEnd
      case Some(ext) => ext
    }

    override def newStmtAtEnd : Extension[PStmt] = _newStmtAtEnd match {
      case None => super.newStmtAtEnd
      case Some(ext) => ext
    }

    override def newStmtAtStart : Extension[PStmt] = _newStmtAtStart match {
      case None => super.newStmtAtStart
      case Some(ext) => ext
    }

    override def newExpAtEnd : Extension[PExp] = _newExpAtEnd match {
      case None => super.newExpAtEnd
      case Some(ext) => ext
    }

    override def newExpAtStart : Extension[PExp] = _newExpAtStart match {
      case None => super.newExpAtStart
      case Some(ext) => ext
    }

    override def postSpecification : Extension[(PReserved[PSpecification], PExp)] = _postSpecification match {
      case None => super.postSpecification
      case Some(ext) => ext
    }

    override def preSpecification : Extension[(PReserved[PSpecification], PExp)] = _preSpecification match {
      case None => super.preSpecification
      case Some(ext) => ext
    }

    override def invSpecification : Extension[(PReserved[PSpecification], PExp)] = _invSpecification match {
      case None => super.invSpecification
      case Some(ext) => ext
    }

    override def extendedKeywords : Set[String] = _extendedKeywords

    def addNewDeclAtEnd(t: Extension[PAnnotationsPosition => PExtender]) : Unit = _newDeclAtEnd match {
      case None => _newDeclAtEnd = Some(t)
      case Some(s) => _newDeclAtEnd = Some(combine(s, t))
    }

    def addNewDeclAtStart(t: Extension[PAnnotationsPosition => PExtender]) : Unit = _newDeclAtStart match {
      case None => _newDeclAtStart = Some(t)
      case Some(s) => _newDeclAtStart = Some(combine(s, t))
    }

    def addNewExpAtEnd(t: Extension[PExp]) : Unit = _newExpAtEnd match {
      case None => _newExpAtEnd = Some(t)
      case Some(s) => _newExpAtEnd = Some(combine(s, t))
    }

    def addNewExpAtStart(t: Extension[PExp]) : Unit = _newExpAtStart match {
      case None => _newExpAtStart = Some(t)
      case Some(s) => _newExpAtStart = Some(combine(s, t))
    }

    def addNewStmtAtEnd(t: Extension[PStmt]) : Unit = _newStmtAtEnd match {
      case None => _newStmtAtEnd = Some(t)
      case Some(s) => _newStmtAtEnd = Some(combine(s, t))
    }

    def addNewStmtAtStart(t: Extension[PStmt]) : Unit = _newStmtAtStart match {
      case None => _newStmtAtStart = Some(t)
      case Some(s) => _newStmtAtStart = Some(combine(s, t))
    }

    def addNewPreCondition(t: Extension[(PReserved[PSpecification], PExp)]) : Unit = _preSpecification match {
      case None => _preSpecification = Some(t)
      case Some(s) => _preSpecification = Some(combine(s, t))
    }

    def addNewPostCondition(t: Extension[(PReserved[PSpecification], PExp)]) : Unit = _postSpecification match {
      case None => _postSpecification = Some(t)
      case Some(s) => _postSpecification = Some(combine(s, t))
    }

    def addNewInvariantCondition(t: Extension[(PReserved[PSpecification], PExp)]) : Unit = _invSpecification match {
      case None => _invSpecification = Some(t)
      case Some(s) => _invSpecification = Some(combine(s, t))
    }

    def addNewKeywords(t : Set[String]) : Unit = {
      _extendedKeywords ++= t
    }
  }
}