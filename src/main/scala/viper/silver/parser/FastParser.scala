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
import viper.silver.parser.FastParserCompanion.{LW, LeadingWhitespace, PositionParsing}
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
      * A parser of the form `(p0 ~ p1.?).pos` or `(p0 ~ p2.rep).pos` may return an end position which
      * includes trailing whitespaces (incl. comments, newlines) if `p1` or `p2` fail to match (the `~` does this).
      * Instead we would like to use `(p0 ~~ (Pass ~ p1).?).pos` or `(p0 ~~ (Pass ~ p2).rep).pos`, which avoids this issue.
      */
    def lw(implicit ctx: P[Any]): LW[T] = new LW(() => Pass ~ p())
    def ~~~[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~ other.p()).asInstanceOf[P[R]]
    def ~~~/[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~/ other.p()).asInstanceOf[P[R]]
  }
  class PositionParsing[T](val p: () => P[((Position, Position)) => T]) extends AnyVal {
    def pos(implicit ctx: P[Any], lineCol: LineCol, _file: Path): P[T] = {
      val startPos = lineCol.getPos(ctx.index)
      val res: P[((Position, Position)) => T] = p()
      val finishPos = lineCol.getPos(ctx.index)
      res.map(_((FilePosition(_file, startPos._1, startPos._2), FilePosition(_file, finishPos._1, finishPos._2))))
    }
  }

  // class Groups[T](val p: () => P[T]) extends AnyVal {
  //   /** `(`...`)` */
  //   def parens(implicit ctx: P[Any]) = FP(PSym.LParen ~ p() ~ PSym.RParen).map {
  //     case (pos, (l, g, r)) => PGrouped[PSym.Paren, T](l, g, r)(pos)
  //   }
  //   /** `<`...`>` */
  //   def angles(implicit ctx: P[Any]) = FP(PSym.LAngle ~ p() ~ PSym.RAngle).map {
  //     case (pos, (l, g, r)) => PGrouped[PSym.Angle, T](l, g, r)(pos)
  //   }
  //   /** `<`...`>` */
  //   def quotes(implicit ctx: P[Any]) = FP(PSym.Quote ~ p() ~ PSym.Quote).map {
  //     case (pos, (l, g, r)) => PGrouped[PSym.Quote.type, T](l, g, r)(pos)
  //   }
  //   /** `{`...`}` */
  //   def braces(implicit ctx: P[Any]) = FP(PSym.LBrace ~ p() ~ PSym.RBrace).map {
  //     case (pos, (l, g, r)) => PGrouped[PSym.Brace, T](l, g, r)(pos)
  //   }
  //   /** `[`...`]` */
  //   def brackets(implicit ctx: P[Any]) = FP(PSym.LBracket ~ p() ~ PSym.RBracket).map {
  //     case (pos, (l, g, r)) => PGrouped[PSym.Bracket, T](l, g, r)(pos)
  //   }
  // }
  // class Delimiters[T <: PNode](val p: () => P[T]) extends AnyVal {
  //   def delim[U <: PSym.Delimit](d: U, min: Int = 0, max: Int = Int.MaxValue, exactly: Int = -1, allowTrailingDelimit: Boolean = false)(implicit ctx: P[Any]) =
  //     FP(
  //       (p() ~ Pass).?.filter(p => (p.isEmpty && min <= 0 && exactly <= 0) || (!p.isEmpty && max > 0 && exactly != 0))
  //     ~~/ (d ~ p()).rep(min = if (min == 0) 0 else min - 1, max = max - 1, exactly = if (exactly == -1) -1 else exactly - 1)
  //     ~~~ d.lw.?
  //     )
  //       .filter(p => p._2._1.isDefined || p._2._2.isEmpty) // Cannot start with delimiter
  //       .filter(p => p._2._3.isEmpty || (p._2._1.isDefined && allowTrailingDelimit)) // Cannot end with delimiter unless `allowTrailingDelimit`
  //       .map {
  //         case (pos, (first, inner, end)) => PDelimited[T, U](first, inner, end)(pos)
  //       }
  // }
  // implicit def Groups[T](p: => P[T]) = new Groups(() => p)
  // implicit def Delimiters[T](p: => P[T]) = new Delimiters(() => p)

  /**
    * A parser which matches leading whitespaces. See `LeadingWhitespace.lw` for more info. Can only be operated on in
    * restricted ways (e.g. `?`, `rep`, `|` or `map`), requiring that it is eventually appened to a normal parser (of type `P[V]`).
    *
    * For example, the following two are equivalent:
    * {{{("hello" ~~~ "world".lw.?).pos
    * ("hello" ~~ (Pass ~ "world").?).pos}}}
    * The type system prevents one from erroneously writing:
    * {{{("hello" ~ "world".lw.?).pos}}}
    */
  class LW[T](val p: () => P[T]) {
    def ?[V](implicit optioner: Implicits.Optioner[T, V], ctx: P[Any]): LW[V] = new LW(() => p().?.asInstanceOf[P[V]])
    def rep[V](min: Int = 0, sep: => P[_] = null, max: Int = Int.MaxValue, exactly: Int = -1)(implicit repeater: Implicits.Repeater[T, V], ctx: P[Any]): LW[V] = new LW(() => p().rep(min, sep, max, exactly).asInstanceOf[P[V]])
    def rep[V](implicit repeater: Implicits.Repeater[T, V], ctx: P[Any]): LW[V] = this.rep()
    def |[V >: T](other: LW[V])(implicit ctx: P[Any]): LW[V] = new LW(() => (p() | other.p()).asInstanceOf[P[V]])
    def filter[V](f: T => Boolean)(implicit ctx: P[Any]): LW[T] = new LW(() => p().filter(f))
    def map[V](f: T => V): LW[V] = new LW(() => p().map(f))
    def ~~[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~ other.p()).asInstanceOf[P[R]]
    def ~~/[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~/ other.p()).asInstanceOf[P[R]]
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

  implicit val lineCol: LineCol = new LineCol(this)

  /* When importing a file from standard library, e.g. `include <inc.vpr>`, the file is expected
   * to be located in `resources/${standard_import_directory}`, e.g. `resources/import/inv.vpr`.
   */
  val standard_import_directory = "import"

  var _line_offset: Array[Int] = null
  /** The file we are currently parsing (for creating positions later). */
  implicit var _file: Path = null
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
            val localPath = current.resolveSibling(ip.file.grouped.inner).normalize()
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
            val standardPath = Paths.get(ip.file.grouped.inner).normalize()
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
  type Pos = (Position, Position)

  lazy val keywords = FastParserCompanion.basicKeywords | ParserExtension.extendedKeywords

  import scala.language.implicitConversions
  implicit def LeadingWhitespaceStr(p: String)(implicit ctx: P[Any]): LeadingWhitespace[Unit] = new LeadingWhitespace(() => P(p))
  implicit def LeadingWhitespace[T](p: => P[T]) = new LeadingWhitespace(() => p)
  implicit def PositionParsing[T](p: => P[Pos => T]) = new PositionParsing(() => p)

  // Actual Parser starts from here
  def identStarts[$: P] = CharIn("A-Z", "a-z", "$_")
  def identContinues[$: P] = CharIn("0-9", "A-Z", "a-z", "$_")

  implicit def reservedKw[$: P, T <: PKeyword](r: T): P[PReserved[T]] = P(P(r.token).map { _ => PReserved(r)(_) } ~~ !identContinues)./.pos
  implicit def reservedSym[$: P, T <: PSymbol](r: T): P[PReserved[T]] = P(r.token./ map { _ => PReserved(r)(_) }).pos

  def reservedSymMany[$: P, T <: PSymbol](clashes: => Option[P[_]], s: => P[_], f: String => T): P[PReserved[T]] =
    P(!clashes.getOrElse(Fail) ~~ s.!./.map { op => PReserved(f(op))(_) }).pos

  /**
    * Parses one of many possible reserved words, should only be used with `StringIn` as `s`. The parser given in
    * `f` should be pre-initialized (e.g. from a `val`), see [here](https://com-lihaoyi.github.io/fastparse/#FlatMap). If only
    * a single reserved word is to be parsed, use `reservedKw` instead.
    */
  def reservedKwMany[$: P, U](s: => P[_], f: String => Pos => P[Pos => U]): P[U] =
    (s.! ~~ !identContinues)./.map(f).pos.flatMap(p => p).pos

  /** `(`...`)` */
  def parens[$: P, T](p: => P[T]) = P((P(PSym.LParen) ~ p ~ PSym.RParen) map (PGrouped.apply[PSym.Paren, T] _).tupled).pos

  /** `()` */
  def emptyParens[$: P] = P((NoCut(PSym.LParen) ~ PSym.RParen) map { case (l, r) => PGrouped[PSym.Paren, Unit](l, (), r)(_) }).pos

  /** `<`...`>` */
  def angles[$: P, T](p: => P[T]) = P((P(PSym.LAngle) ~ p ~ PSym.RAngle) map (PGrouped.apply[PSym.Angle, T] _).tupled).pos

  /** `<`...`>` */
  def quotes[$: P, T](p: => P[T]) = P((P(PSym.Quote) ~ p ~ PSym.Quote) map (PGrouped.apply[PSym.Quote.type, T] _).tupled).pos

  /** `{`...`}` */
  def braces[$: P, T](p: => P[T]) = P((P(PSym.LBrace) ~ p ~ PSym.RBrace) map (PGrouped.apply[PSym.Brace, T] _).tupled).pos

  /** `[`...`]` */
  def brackets[$: P, T](p: => P[T]) = P((P(PSym.LBracket) ~ p ~ PSym.RBracket) map (PGrouped.apply[PSym.Bracket, T] _).tupled).pos

  def rep[$: P, T, U](p: => P[T], sep: => P[U], min: Int = 0, max: Int = Int.MaxValue, exactly: Int = -1, allowTrailingDelimit: Boolean = false) =
    P((    (p ~ Pass).lw.?.filter(p => (p.isEmpty && min <= 0 && exactly <= 0) || (!p.isEmpty && max > 0 && exactly != 0)) // Parse first element
       ~~/ (sep ~ p).lw.rep(min = if (min == 0) 0 else min - 1, max = max - 1, exactly = if (exactly == -1) -1 else exactly - 1) // Parse other elements
       ~~~ sep.lw.? // Parse trailing delimiter
      ).filter(p => p._1.isDefined || p._2.isEmpty) // Cannot start with delimiter
       .filter(p => p._3.isEmpty || (p._1.isDefined && allowTrailingDelimit)) // Cannot end with delimiter unless `allowTrailingDelimit`
       .map( (PDelimited.apply[T, U] _).tupled )
    ).pos

  /** `(`...`,` ...`,` ...`)` */
  def argList[$: P, T <: PNode](p: => P[T]) = parens(rep(p, PSym.Comma))

  /** `[`...`,` ...`,` ...`]` */
  def typeList[$: P, T <: PNode](p: => P[T]) = brackets(rep(p, PSym.Comma))

  def foldPExp[E <: PExp](e: E, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) => a(t) }

  def atomReservedKw[$: P]: P[PExp] = reservedKwMany(
    StringIn("true", "false", "null", "old", "result", "acc", "none", "wildcard", "write", "epsilon", "perm", "let", "forall", "exists", "forperm",
      "unfolding", "applying", "Set", "Seq", "Multiset", "Map", "range", "domain", "new"),
    str => pos => str match {
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

  def atomParen[$: P](bracketed: Boolean = false): P[PExp] = P(parens(expParen(true)).map(g => { g.inner.brackets = Some(g); g.inner }) | atom(bracketed))

  def stringLiteral[$: P]: P[PStringLiteral] = P((quotes(CharsWhile(_ != '\"').!)) map (PStringLiteral.apply _)).pos

  def annotation[$: P]: P[PAnnotation] = P((P(PSym.At) ~~ annotationIdentifier ~ argList(stringLiteral)) map (PAnnotation.apply _).tupled).pos

  def annotated[$: P, T](inner: => P[PAnnotationsPosition => T]): P[T] = P((annotation.rep(0) ~ inner).map {
    case (annotations, i) => pos: Pos => i(PAnnotationsPosition(annotations, pos))
  }).pos

  def annotatedAtom[$: P]: P[PExp] = P((annotation ~ atomParen()) map (PAnnotatedExp.apply _).tupled).pos

  def result[$: P]: P[PResultLit] = P(P(PKw.Result) map (PResultLit.apply _)).pos

  def unExp[$: P]: P[PUnExp] = P(((P(PSymOp.Neg) | PSymOp.Not) ~ suffixExpr()) map (PUnExp.apply _).tupled).pos

  def strInteger[$: P]: P[String] = P(CharIn("0-9").rep(1)).!

  def integer[$: P]: P[PIntLit] = P((strInteger.filter(s => s.matches("\\S+"))) map (s => PIntLit(BigInt(s))(_))).pos

  def identifier[$: P]: P[Unit] = identStarts ~~ identContinues.repX

  def annotationIdentifier[$: P]: P[PIdnRef] = P(((identStarts ~~ CharIn("0-9", "A-Z", "a-z", "$_.").repX).!) map (PIdnRef.apply _)).pos

  def ident[$: P]: P[String] = identifier.!.filter(a => !keywords.contains(a)).opaque("identifier")

  def idnuse[$: P]: P[PIdnUseExp] = P((ident) map (PIdnUseExp.apply _)).pos

  def idnref[$: P]: P[PIdnRef] = P((ident) map (PIdnRef.apply _)).pos

  def oldLabel[$: P]: P[PLabelUse] = P((P(PKw.Lhs) map (PLhsLabel.apply _)).pos | idnuse)

  def old[$: P](k: PReserved[PKwOp.Old.type]): P[Pos => POldExp] = P(brackets(oldLabel).? ~ parens(exp)).map {
    case (lbl, g) => POldExp(k, lbl, g)
  }

  def magicWandExp[$: P](bracketed: Boolean = false): P[PExp] = P((orExp(bracketed) ~~~ (P(PSymOp.Wand) ~ exp).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (op, rhs) => PMagicWandExp(lhs, op, rhs)(pos) }.getOrElse(lhs)
  }).pos

  def realMagicWandExp[$: P]: P[PMagicWandExp] = P((orExp() ~ PSymOp.Wand ~ exp) map (PMagicWandExp.apply _).tupled).pos

  def implExp[$: P](bracketed: Boolean = false): P[PExp] = P((magicWandExp(bracketed) ~~~ (P(PSymOp.Implies) ~ implExp()).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (op, rhs) => PBinExp(lhs, op, rhs)(pos) }.getOrElse(lhs)
  }).pos

  def iffExp[$: P](bracketed: Boolean = false): P[PExp] = P((implExp(bracketed) ~~~ (P(PSymOp.Iff) ~ iffExp()).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (op, rhs) => PBinExp(lhs, op, rhs)(pos) }.getOrElse(lhs)
  }).pos

  def iteExpr[$: P](bracketed: Boolean = false): P[PExp] = P((iffExp(bracketed) ~~~ (P(PSymOp.Question) ~ iteExpr() ~ PSymOp.Colon ~ iteExpr()).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (q, thn, c, els) => PCondExp(lhs, q, thn, c, els)(pos) }.getOrElse(lhs)
  }).pos

  /** Expression which had parens around it if `bracketed` is true */
  def expParen[$: P](bracketed: Boolean): P[PExp] = P(iteExpr(bracketed))

  def exp[$: P]: P[PExp] = P(expParen(false))

  /** Expression should be parenthesized (e.g. for `if (exp)`). We could consider making these parentheses optional in the future. */
  def parenthesizedExp[$: P]: P[PExp] = parens(exp).map(g => { g.inner.brackets = Some(g); g.inner })

  def indexSuffix[$: P]: P[(PReserved[PSymOp.LBracket.type], PExp, PReserved[PSymOp.RBracket.type]) => Pos => SuffixedExpressionGenerator[PExp]] = P(
    (P(PSymOp.Assign) ~ exp).map { case (a, v) => (l: PReserved[PSymOp.LBracket.type], i: PExp, r: PReserved[PSymOp.RBracket.type]) => pos: Pos
      => SuffixedExpressionGenerator[PExp](e => PUpdate(e, l, i, a, v, r)(e.pos._1, pos._2)) } |
    (P(PSymOp.DotDot) ~ exp.?).map { case (d, m) => (l: PReserved[PSymOp.LBracket.type], n: PExp, r: PReserved[PSymOp.RBracket.type]) => pos: Pos
      => SuffixedExpressionGenerator[PExp](e => PSeqSlice(e, l, Some(n), d, m, r)(e.pos._1, pos._2)) } |
    Pass.map { _ => (l: PReserved[PSymOp.LBracket.type], e1: PExp, r: PReserved[PSymOp.RBracket.type]) => pos: Pos
      => SuffixedExpressionGenerator[PExp](e0 => PLookup(e0, l, e1, r)(e0.pos._1, pos._2)) })

  def fieldAccess[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(((!P(PSymOp.DotDot) ~~ PSymOp.Dot) ~ idnref) map { case (dot, id) => pos: Pos => SuffixedExpressionGenerator[PExp](e => PFieldAccess(e, dot, id)(e.pos._1, pos._2)) }).pos

  def sliceEnd[$: P]: P[((PReserved[PSymOp.LBracket.type], PReserved[PSymOp.RBracket.type])) => Pos => SuffixedExpressionGenerator[PExp]] =
    P((P(PSymOp.DotDot) ~ exp).map { case (d, n) => b => pos: Pos
          => SuffixedExpressionGenerator[PExp](e => PSeqSlice(e, b._1, None, d, Some(n), b._2)(e.pos._1, pos._2)) })

  def indexContinue[$: P]: P[((PReserved[PSymOp.LBracket.type], PReserved[PSymOp.RBracket.type])) => Pos => SuffixedExpressionGenerator[PExp]] =
    P((exp ~ indexSuffix).map { case (e, s) => b => s(b._1, e, b._2) })

  def index[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P((P(PSymOp.LBracket) ~ (sliceEnd | indexContinue) ~ PSymOp.RBracket) map { case (l, f, r) => f(l, r) }).pos

//  map (.apply _).tupled).pos
  def suffix[$: P]: P[SuffixedExpressionGenerator[PExp]] = P(fieldAccess | index)

  def suffixExpr[$: P](bracketed: Boolean = false): P[PExp] = P((atomParen(bracketed) ~~~ suffix.lw.rep).map { case (fac, ss) => foldPExp(fac, ss) })

  def termOp[$: P] = P(reservedSymMany(None, StringIn("*", "/", "\\", "%"), _ match {
    case "*" => PSymOp.Mul
    case "/" => PSymOp.Div
    case "\\" => PSymOp.ArithDiv
    case "%" => PSymOp.Mod
  }))

  def term[$: P](bracketed: Boolean = false): P[PExp] = P((suffixExpr(bracketed) ~~~ termd.lw.rep).map { case (a, ss) => foldPExp(a, ss) })

  def termd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = P((termOp ~ suffixExpr()) map { case (op, id) => pos: Pos => SuffixedExpressionGenerator(e => PBinExp(e, op, id)(e.pos._1, pos._2)) }).pos

  def sumOp[$: P]: P[PReserved[PBinaryOp]] = P(reservedSymMany(Some("--*"), StringIn("++", "+", "-"), _ match {
    case "++" => PSymOp.Append
    case "+" => PSymOp.Plus
    case "-" => PSymOp.Minus
  }) | reservedKwMany(StringIn("union", "intersection", "setminus", "subset"), str => _ => str match {
    case "union" => Pass.map(_ => PReserved(PKwOp.Union))
    case "intersection" => Pass.map(_ => PReserved(PKwOp.Intersection))
    case "setminus" => Pass.map(_ => PReserved(PKwOp.Setminus))
    case "subset" => Pass.map(_ => PReserved(PKwOp.Subset))
  }))

  def sum[$: P](bracketed: Boolean = false): P[PExp] = P((term(bracketed) ~~~ sumd.lw.rep).map { case (a, ss) => foldPExp(a, ss) })

  def sumd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = P((sumOp ~ term()).map { case (op, id) => pos: Pos => SuffixedExpressionGenerator(e => PBinExp(e, op, id)(e.pos._1, pos._2)) }).pos

  def cmpOp[$: P]: P[PReserved[PBinaryOp]] = P(reservedSymMany(Some("<==>"), StringIn("<=", ">=", "<", ">"), _ match {
    case "<=" => PSymOp.Le
    case ">=" => PSymOp.Ge
    case "<" => PSymOp.Lt
    case ">" => PSymOp.Gt
  }) | PKwOp.In)

  val cmpOps = Set("<=", ">=", "<", ">", "in")

  def cmpd[$: P]: P[PExp => SuffixedExpressionGenerator[PBinExp]] = P((cmpOp ~ sum()).map {
    case (op, right) => chainComp(op, right) _
  }).pos

  def chainComp(op: PReserved[PBinaryOp], right: PExp)(pos: Pos)(from: PExp) = SuffixedExpressionGenerator(_ match {
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

  def eqExpParen[$: P](bracketed: Boolean = false): P[PExp] = P((cmpExp(bracketed) ~~~ (eqOp ~ eqExp).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (op, rhs) => PBinExp(lhs, op, rhs)(pos) }.getOrElse(lhs)
  }).pos
  def eqExp[$: P]: P[PExp] = eqExpParen()

  def andExp[$: P](bracketed: Boolean = false): P[PExp] = P((eqExpParen(bracketed) ~~~ (P(PSymOp.AndAnd) ~ andExp()).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (op, rhs) => PBinExp(lhs, op, rhs)(pos) }.getOrElse(lhs)
  }).pos

  def orExp[$: P](bracketed: Boolean = false): P[PExp] = P((andExp(bracketed) ~~~ (P(PSymOp.OrOr) ~ orExp()).lw.?).map {
    case (lhs, b) => pos: Pos => b.map { case (op, rhs) => PBinExp(lhs, op, rhs)(pos) }.getOrElse(lhs)
  }).pos

  def pairArgument[$: P, T, U](t: => P[T], u: => P[U]): P[PPairArgument[T, U]] =
    P((t ~ P(PSym.Comma) ~ u) map (PPairArgument.apply[T, U] _).tupled).pos

  def maybePairArgument[$: P, T, U](t: => P[T], u: => P[U]): P[PMaybePairArgument[T, U]] =
    P((t ~~~ (P(PSym.Comma) ~ u).lw.?)
        map (PMaybePairArgument.apply[T, U] _).tupled).pos

  def accessPredImpl[$: P](k: PReserved[PKwOp.Acc.type]): P[Pos => PAccPred] = P(parens(maybePairArgument(locAcc, exp)) map (PAccPred(k, _) _))

  def accessPred[$: P]: P[PAccPred] = P(P(PKwOp.Acc).flatMap(accessPredImpl(_))).pos

  def resAcc[$: P]: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  def locAcc[$: P]: P[PLocationAccess] = P(fieldAcc | predAcc)

  def fieldAcc[$: P]: P[PFieldAccess] =
    P(NoCut(suffixExpr()) flatMap {
      case fa: PFieldAccess => Pass.map(_ => fa)
      case _ => Fail
    })

  def predAcc[$: P]: P[PCall] = funcApp

  def inhaleExhale[$: P]: P[PExp] = P((P(PSymOp.LBracket) ~ NoCut(exp) ~ PSymOp.Comma ~ exp ~ PSymOp.RBracket) map (PInhaleExhaleExp.apply _).tupled).pos

  def perm[$: P](k: PReserved[PKwOp.Perm.type]): P[Pos => PCurPerm] = P(parens(resAcc)).map(PCurPerm(k, _))

  def let[$: P](k: PReserved[PKwOp.Let.type]): P[Pos => PExp] =
    P(idndef ~ PSymOp.EqEq ~ parenthesizedExp ~ PKwOp.In ~ exp).map {
      case (id, eq, exp1, in, exp2) =>
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

  def idndef[$: P]: P[PIdnDef] = P(ident map (PIdnDef.apply _)).pos

  def forall[$: P](k: PReserved[PKw.Forall.type]): P[Pos => PExp] = P(nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ PSym.ColonColon ~ trigger.rep ~ exp).map {
    case (a, o, b, c) =>
      PForall(k, a, o, b, c)
    }
  def exists[$: P](k: PReserved[PKw.Exists.type]): P[Pos => PExp] = P(nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ PSym.ColonColon ~ trigger.rep ~ exp).map {
    case (a, o, b, c) =>
      PExists(k, a, o, b, c)
    }

  def nonEmptyIdnTypeList[$: P, T](f: PIdnTypeBinding => T): P[PDelimited[T, PSym.Comma]] = P(rep(idnTypeBinding map f, PSym.Comma, min = 1))

  def idnTypeBinding[$: P]: P[PIdnTypeBinding] = P((idndef ~ PSym.Colon ~ typ) map (PIdnTypeBinding.apply _).tupled).pos

  def typReservedKw[$: P]: P[PType] = reservedKwMany(
    StringIn("Rational", "Int", "Bool", "Perm", "Ref", "Seq", "Set", "Multiset", "Map"),
    str => pos => str match {
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

  def domainTyp[$: P]: P[PDomainType] = P((idnref ~~~ typeList(typ).lw.?) map (PDomainType.apply _).tupled).pos

  def seqType[$: P](k: PReserved[PKw.Seq.type]): P[Pos => PSeqType] = P(brackets(typ) map { case t => PSeqType(k, t) })

  def setType[$: P](k: PReserved[PKw.Set.type]): P[Pos => PSetType] = P(brackets(typ) map { case t => PSetType(k, t) })

  def multisetType[$: P](k: PReserved[PKw.Multiset.type]): P[Pos => PMultisetType] = P(brackets(typ) map { case t => PMultisetType(k, t) })

  def mapType[$: P](k: PReserved[PKw.Map.type]): P[Pos => PMapType] = P(brackets(pairArgument(typ, typ)) map { case t => PMapType(k, t)})

  /** Only for call-like macros, `idnuse`-like ones are parsed by `domainTyp`. */
  def macroType[$: P] : P[PMacroType] = funcApp.map(PMacroType(_))

  def trigger[$: P]: P[PTrigger] = P(braces(rep(exp, PSym.Comma)) map (PTrigger.apply _)).pos

  def forperm[$: P](k: PReserved[PKw.Forperm.type]): P[Pos => PExp] = P(nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ brackets(resAcc) ~ PSym.ColonColon ~ exp).map {
    case (args, res, op, body) => PForPerm(k, args, res, op, body)
  }

  def unfolding[$: P](k: PReserved[PKwOp.Unfolding.type]): P[Pos => PExp] = P(predicateAccessAssertion ~ PKwOp.In ~ exp).map {
    case (a, in, b) => PUnfolding(k, a, in, b)
  }

  def applying[$: P](k: PReserved[PKwOp.Applying.type]): P[Pos => PExp] = P(parens(magicWandExp()) ~ PKwOp.In ~ exp).map {
    case (wand, op, b) =>
      wand.inner.brackets = Some(wand)
      PApplying(k, wand.inner, op, b)
  }

  def predicateAccessAssertion[$: P]: P[PAccAssertion] = P(accessPred | predAcc)

  def setConstructor[$: P](k: PReserved[PKwOp.Set.type]): P[Pos => PExp] =
    builtinConstructor(typ, exp)(
      { case (t, g) => PEmptySet(k, t, g) },
      { case t => PExplicitSet(k, t) }
    )

  def seqConstructor[$: P](k: PReserved[PKwOp.Seq.type]): P[Pos => PExp] =
    builtinConstructor(typ, exp)(
      { case (t, g) => PEmptySeq(k, t, g) },
      { case t => PExplicitSeq(k, t) }
    )

  def multisetConstructor[$: P](k: PReserved[PKwOp.Multiset.type]): P[Pos => PExp] =
    builtinConstructor(typ, exp)(
      { case (t, g) => PEmptyMultiset(k, t, g) },
      { case t => PExplicitMultiset(k, t) }
    )

  def mapConstructor[$: P](k: PReserved[PKwOp.Map.type]): P[Pos => PExp] =
    builtinConstructor(pairArgument(typ, typ), maplet)(
      { case (t, g) => PEmptyMap(k, t, g) },
      { case t => PExplicitMap(k, t) }
    )

  def builtinConstructor[$: P, T, E <: PNode](types: => P[T], element: => P[E])(
    empty: ((Option[PGrouped[PSym.Bracket, T]], PGrouped[PSym.Paren, Unit])) => Pos => PExp,
    nonEmpty: (PSym.Punctuated[PSym.Paren, E]) => Pos => PExp
  ): P[Pos => PExp] =
    P(((brackets(types)).? ~ emptyParens).map(empty) | (parens(rep(element, PSym.Comma, 1))).map(nonEmpty))

  def size[$: P]: P[PExp] = P((P(PSymOp.Or) ~ exp ~ PSymOp.Or) map (PSize.apply _).tupled).pos

  def seqRange[$: P]: P[PExp] = P((P(PSymOp.LBracket) ~ NoCut(exp) ~ PSymOp.DotDot ~ exp ~ PSymOp.RParen).map((PRangeSeq.apply _).tupled).pos)

  def maplet[$: P]: P[PMaplet] = P((exp ~ PSymOp.Assign ~ exp) map (PMaplet.apply _).tupled).pos

  def mapDomain[$: P](k: PReserved[PKwOp.Domain.type]): P[Pos => PMapDomain] = P(parens(exp)).map {
    case e => PMapDomain(k, e)
  }

  def mapRange[$: P](k: PReserved[PKwOp.Range.type]): P[Pos => PMapRange] = P(parens(exp)).map {
    case e => PMapRange(k, e)
  }

  def newExp[$: P](k: PReserved[PKw.New.type]): P[Pos => PNewExp] = P(parens(newExpFields) map (PNewExp(k, _) _))

  def newExpFields[$: P]: P[Either[PSym.Star, PDelimited[PIdnUseExp, PSym.Comma]]] = P(P(PSym.Star).map(Left(_)) | P(rep(idnuse, PSym.Comma).map(Right(_))))

  def funcApp[$: P]: P[PCall] = P((idnref ~ argList(exp)) map {
    case (func, args) => PCall(func, args, None)(_)
  }).pos

  def maybeTypedFuncApp[$: P](bracketed: Boolean): P[PCall] = P(if (!bracketed) funcApp else (funcApp ~~~ (P(PSym.Colon) ~ typ).lw.?).map {
    case (func, typeGiven) => func.copy(typeAnnotated = typeGiven)(_)
  }.pos)

  def stmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | annotatedStmt |
    fold | unfold | exhale | assertStmt |
    inhale | assume | ifThenElse | whileStmt | localVars | defineDeclStmt |
    goto | label | packageWand | applyWand | stmtBlock |
    quasihavoc | quasihavocall | assign | methodCall | ParserExtension.newStmtAtEnd(ctx))

  def annotatedStmt(implicit ctx : P[_]): P[PStmt] = P((annotation ~ stmt) map (PAnnotatedStmt.apply _).tupled).pos

  def nodefinestmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | annotatedStmt |
    fold | unfold | exhale | assertStmt |
    inhale | assume | ifThenElse | whileStmt | localVars |
    goto | label | packageWand | applyWand | stmtBlock |
    quasihavoc | quasihavocall | assign | methodCall | ParserExtension.newStmtAtEnd(ctx))

  def assignTarget[$: P]: P[PAssignTarget] = P(fieldAcc | NoCut(funcApp) | idnuse)

  def assign[$: P]: P[PAssign] = P((rep(assignTarget, PSym.Comma, min = 1) ~ P(PSymOp.Assign).map(Some(_)) ~ exp) map (PAssign.apply _).tupled).pos

  // The `rep(Fail, Fail)` produces an empty list of targets and the `Pass` produces a `None: Option[PSymOp.Assign]` (i.e. both consume no characters)
  def methodCall[$: P]: P[PAssign] = P((rep(Fail, Fail) ~~ Pass.map(_ => None) ~~ (funcApp | idnuse)) map (PAssign.apply _).tupled).pos

  def fold[$: P]: P[PFold] = P((P(PKw.Fold) ~ predicateAccessAssertion) map (PFold.apply _).tupled).pos

  def unfold[$: P]: P[PUnfold] = P((P(PKw.Unfold) ~ predicateAccessAssertion) map (PUnfold.apply _).tupled).pos

  def exhale[$: P]: P[PExhale] = P((P(PKw.Exhale) ~ exp) map (PExhale.apply _).tupled).pos

  def assertStmt[$: P]: P[PAssert] = P((P(PKw.Assert) ~ exp) map (PAssert.apply _).tupled).pos

  def inhale[$: P]: P[PInhale] = P((P(PKw.Inhale) ~ exp) map (PInhale.apply _).tupled).pos

  def assume[$: P]: P[PAssume] = P((P(PKw.Assume) ~ exp) map (PAssume.apply _).tupled).pos

  // Parsing Havoc statements
  // Havoc statements have two forms:
  // in the grammar. Note that it is still possible to express "(<exp1> ==> <exp2>) ==> <resource>
  // using parentheses.

  // Havocall follows a similar pattern to havoc but allows quantifying over variables.

  def quasihavoc[$: P]: P[PQuasihavoc] =
    P((P(PKw.Quasihavoc) ~ (NoCut(magicWandExp()) ~ PSymOp.Implies).? ~ exp) map (PQuasihavoc.apply _).tupled).pos

  def quasihavocall[$: P]: P[PQuasihavocall] =
    P((P(PKw.Quasihavocall) ~ nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ PSym.ColonColon ~ (NoCut(magicWandExp()) ~ PSymOp.Implies).? ~ exp)
      map (PQuasihavocall.apply _).tupled).pos

  def ifThenElse[$: P]: P[PIf] = P((P(PKw.If) ~ parenthesizedExp ~ stmtBlock ~~~ elseIfOrElse.lw.?) map (PIf.apply _).tupled).pos

  def stmtBlock[$: P]: P[PSeqn] =  P(braces(rep(stmt, P(PSym.Semi).?./)) map (PSeqn.apply _)).pos
  def nodefinestmtBlock[$: P]: P[PSeqn] =  P(braces(rep(nodefinestmt, P(PSym.Semi).?./)) map (PSeqn.apply _)).pos

  def elseIfOrElse[$: P]: P[PIfContinuation] = elseIf | elseBlock

  def elseIf[$: P]: P[PIf] = P((P(PKw.Elseif) ~ parenthesizedExp ~ stmtBlock ~~~ elseIfOrElse.lw.?) map (PIf.apply _).tupled).pos

  def elseBlock[$: P]: P[PElse] =
    P((P(PKw.Else) ~ stmtBlock) map (PElse.apply _).tupled).pos

  def whileStmt[$: P]: P[PWhile] = P((P(PKw.While) ~ parenthesizedExp ~ rep(invariant, P(PSym.Semi).?, allowTrailingDelimit = true) ~ stmtBlock) map (PWhile.apply _).tupled).pos

  def invariant(implicit ctx : P[_]) : P[PSpecification[PKw.InvSpec]] = P((P(PKw.Invariant) ~ exp).map((PSpecification.apply _).tupled).pos | ParserExtension.invSpecification(ctx))

  def localVars[$: P]: P[PVars] =
    P((P(PKw.Var) ~ nonEmptyIdnTypeList(PLocalVarDecl(_)) ~~~ (P(PSymOp.Assign) ~ exp).lw.?) map (PVars.apply _).tupled).pos

  def defineDecl[$: P]: P[PAnnotationsPosition => PDefine] =
    P((P(PKw.Define) ~ idndef ~ parens(rep(idndef, PSym.Comma)).? ~ (nodefinestmtBlock | exp)) map {
      case (k, idn, args, body) => ap: PAnnotationsPosition => PDefine(ap.annotations, k, idn, args, body)(ap.pos)
    })

  def defineDeclStmt[$: P]: P[PDefine] = P(defineDecl.map { f => pos: Pos => f(PAnnotationsPosition(Nil, pos)) }).pos

  def goto[$: P]: P[PGoto] = P((P(PKw.Goto) ~ idnuse) map (PGoto.apply _).tupled).pos

  def label[$: P]: P[PLabel] = P((P(PKw.Label) ~ idndef ~ rep(invariant, P(PSym.Semi).?, allowTrailingDelimit = true)) map (PLabel.apply _).tupled).pos

  def packageWand[$: P]: P[PPackageWand] = P((P(PKw.Package) ~ magicWandExp() ~~~ stmtBlock.lw.?) map (PPackageWand.apply _).tupled).pos

  def applyWand[$: P]: P[PApplyWand] = P((P(PKw.Apply) ~ magicWandExp()) map (PApplyWand.apply _).tupled).pos

  def programMember(implicit ctx : P[_]): P[PNode] = annotated(ParserExtension.newDeclAtStart(ctx) | preambleImport | defineDecl | fieldDecl | methodDecl | domainDecl | functionDecl | predicateDecl | ParserExtension.newDeclAtEnd(ctx))

  def programDecl[$: P]: P[PProgram] =
    P(programMember.rep.map {
    case decls => {
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
      )(_)
    }
  }).pos

  def preambleImport[$: P]: P[PAnnotationsPosition => PImport] = P(P(PKw.Import) ~
    (quotes(relativeFilePath).map { case s => pos: Pos => (true, PStringLiteral(s)(pos)) }
   | angles(relativeFilePath).map { case s => pos: Pos => (false, PStringLiteral(s)(pos)) }).pos
  ).map {
    case (k, (local, filename)) => ap: PAnnotationsPosition => PImport(ap.annotations, k, local, filename)(ap.pos)
  }

  def relativeFilePath[$: P]: P[String] = (CharIn("~.").? ~~ (CharIn("/").? ~~ CharIn(".", "A-Z", "a-z", "0-9", "_\\- \n\t")).rep(1)).!

  def domainInterp[$: P]: P[PDomainInterpretation] = P((ident ~ PSym.Colon ~ stringLiteral) map (PDomainInterpretation.apply _).tupled).pos
  def domainInterps[$: P]: P[PDomainInterpretations] =
    P((P(PKw.Interpretation) ~ parens(rep(domainInterp, PSym.Comma))) map (PDomainInterpretations.apply _).tupled).pos

  def domainDecl[$: P]: P[PAnnotationsPosition => PDomain] = P(P(PKw.Domain) ~ idndef ~ typeParams.? ~ domainInterps.? ~
    braces((annotated(domainFunctionDecl | axiomDecl).rep map (PDomainMembers1.apply _)).pos)).map {
    case (k, name, typparams, interpretations, block) =>
      val members = block.inner.members
      val funcs1 = members collect { case m: PDomainFunction1 => m }
      val axioms1 = members collect { case m: PAxiom1 => m }
      val funcs = funcs1 map (f => PDomainFunction(f.annotations, f.unique, f.function, f.sig, f.c, f.typ, f.interpretation, f.s)(PIdnRef(name.name)(name.pos))(f.pos))
      val axioms = axioms1 map (a => PAxiom(a.annotations, a.axiom, a.idndef, a.exp, a.s)(PIdnRef(name.name)(name.pos))(a.pos))
      ap: PAnnotationsPosition => PDomain(
        ap.annotations,
        k,
        name,
        typparams,
        PDomainMembers(funcs, axioms)(block.pos),
        interpretations)(ap.pos)
  }

  def domainTypeVarDecl[$: P]: P[PTypeVarDecl] = P(idndef map (PTypeVarDecl.apply _)).pos

  def typeParams[$: P]: P[PSym.Punctuated[PSym.Bracket, PTypeVarDecl]] = P(brackets(rep(domainTypeVarDecl, PSym.Comma)))

  def domainFunctionDecl[$: P]: P[PAnnotationsPosition => PDomainFunction1] = P(P(PKw.Unique).? ~ domainFunctionSignature ~ (P(PKw.Interpretation) ~ stringLiteral).? ~~~ P(PSym.Semi).lw.?).map {
    case (unique, (function, sig, c, typ), interpretation, s) => ap: PAnnotationsPosition => PDomainFunction1(ap.annotations, unique, function, sig, c, typ, interpretation, s)(ap.pos)

  }

  def domainFunctionSignature[$: P] = P(P(PKw.Function) ~ signature(formalArg | unnamedFormalArg) ~ PSym.Colon ~ typ)

  def formalArg[$: P]: P[PFormalArgDecl] = P(idnTypeBinding.map(PFormalArgDecl(_)))

  def unnamedFormalArg[$: P] = P(typ map (PUnnamedFormalArgDecl.apply _)).pos

  def formalReturnList[$: P]: P[PDelimited[PFormalReturnDecl, PSym.Comma]] = P(rep(idnTypeBinding.map(PFormalReturnDecl(_)), PSym.Comma))

  def signature[$: P, T <: PAnyFormalArgDecl](p: => P[T]): P[PSignature[T]] = P((idndef ~ parens(rep(p, PSym.Comma))) map (PSignature.apply[T] _).tupled).pos

  def axiomDecl[$: P]: P[PAnnotationsPosition => PAxiom1] = P(P(PKw.Axiom) ~ idndef.? ~ braces(exp) ~~~ P(PSym.Semi).lw.?).map { case (k, a, b, s) =>
    ap: PAnnotationsPosition => PAxiom1(ap.annotations, k, a, b, s)(ap.pos)
  }

  def fieldDecl[$: P]: P[PAnnotationsPosition => PFields] = P(P(PKw.Field) ~ nonEmptyIdnTypeList(PFieldDecl(_)) ~~~ P(PSym.Semi).lw.?).map {
    case (k, a, s) => ap: PAnnotationsPosition => PFields(ap.annotations, k, a, s)(ap.pos)
  }

  def functionDecl[$: P]: P[PAnnotationsPosition => PFunction] = P(P(PKw.Function) ~ signature(formalArg) ~ PSym.Colon ~ typ
    ~~ rep(precondition, P(PSym.Semi).?, allowTrailingDelimit = true)
    ~~ rep(postcondition, P(PSym.Semi).?, allowTrailingDelimit = true) ~~~ braces(exp).lw.?
  ).map({ case (k, sig, c, typ, d, e, f) =>
      ap: PAnnotationsPosition => PFunction(ap.annotations, k, sig, c, typ, d, e, f)(ap.pos)
  })


  def precondition(implicit ctx : P[_]) : P[PSpecification[PKw.PreSpec]] = P((P(PKw.Requires) ~ exp).map((PSpecification.apply _).tupled).pos | ParserExtension.preSpecification(ctx))

  def postcondition(implicit ctx : P[_]) : P[PSpecification[PKw.PostSpec]] = P((P(PKw.Ensures) ~ exp).map((PSpecification.apply _).tupled).pos | ParserExtension.postSpecification(ctx))

  def predicateDecl[$: P]: P[PAnnotationsPosition => PPredicate] = P(P(PKw.Predicate) ~ signature(formalArg) ~~~ (braces(exp)).lw.?).map {
    case (k, sig, c) =>
      ap: PAnnotationsPosition => PPredicate(ap.annotations, k, sig, c)(ap.pos)
  }

  def methodDecl[$: P]: P[PAnnotationsPosition => PMethod] = P(methodSignature ~~ rep(precondition, P(PSym.Semi).?, allowTrailingDelimit = true) ~~ rep(postcondition, P(PSym.Semi).?, allowTrailingDelimit = true) ~~~ stmtBlock.lw.?).map {
    case (k, sig, rets, pres, posts, body) =>
      ap: PAnnotationsPosition => PMethod(ap.annotations, k, sig, rets, pres, posts, body)(ap.pos)
  }

  def methodSignature[$: P] = P(P(PKw.Method) ~ signature(formalArg) ~~~ methodReturns.lw.?)

  def methodReturns[$: P]: P[PMethodReturns] = P((P(PKw.Returns) ~ parens(formalReturnList)) map (PMethodReturns.apply _).tupled).pos

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

    private var _preSpecification: Option[Extension[PSpecification[PKw.PreSpec]]] = None
    private var _postSpecification: Option[Extension[PSpecification[PKw.PostSpec]]] = None
    private var _invSpecification: Option[Extension[PSpecification[PKw.InvSpec]]] = None

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

    override def preSpecification : Extension[PSpecification[PKw.PreSpec]] = _preSpecification match {
      case None => super.preSpecification
      case Some(ext) => ext
    }

    override def postSpecification : Extension[PSpecification[PKw.PostSpec]] = _postSpecification match {
      case None => super.postSpecification
      case Some(ext) => ext
    }

    override def invSpecification : Extension[PSpecification[PKw.InvSpec]] = _invSpecification match {
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

    def addNewPreCondition(t: Extension[PSpecification[PKw.PreSpec]]) : Unit = _preSpecification match {
      case None => _preSpecification = Some(t)
      case Some(s) => _preSpecification = Some(combine(s, t))
    }

    def addNewPostCondition(t: Extension[PSpecification[PKw.PostSpec]]) : Unit = _postSpecification match {
      case None => _postSpecification = Some(t)
      case Some(s) => _postSpecification = Some(combine(s, t))
    }

    def addNewInvariantCondition(t: Extension[PSpecification[PKw.InvSpec]]) : Unit = _invSpecification match {
      case None => _invSpecification = Some(t)
      case Some(s) => _invSpecification = Some(combine(s, t))
    }

    def addNewKeywords(t : Set[String]) : Unit = {
      _extendedKeywords ++= t
    }
  }
}