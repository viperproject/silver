// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.net.URL
import java.nio.file.{Path, Paths}
import viper.silver.ast.{FilePosition, LineCol, NoPosition, SourcePosition}
import viper.silver.ast.utility.{DiskLoader, FileLoader}
import viper.silver.plugin.{ParserPluginTemplate, SilverPluginManager}
import viper.silver.verifier.{ParseError, ParseWarning}

import scala.collection.{immutable, mutable}
import scala.util.{Failure, Success}
import viper.silver.ast.HasLineColumn

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

  def identStarts[$: P] = CharIn("A-Z", "a-z", "$_")
  def identContinues[$: P] = CharIn("0-9", "A-Z", "a-z", "$_")

  type Pos = (FilePosition, FilePosition)
  import scala.language.implicitConversions
  implicit def LeadingWhitespaceStr[$: P](p: String): LeadingWhitespace[Unit] = new LeadingWhitespace(() => P(p))
  implicit def LeadingWhitespace[T](p: => P[T]) = new LeadingWhitespace(() => p)
  implicit def PositionParsing[T](p: => P[Pos => T]) = new PositionParsing(() => p)
  implicit def ExtendedParsing[T](p: => P[T]) = new ExtendedParsing(() => p)
  implicit def reservedKw[$: P, T <: PKeyword](r: T)(implicit lineCol: LineCol, _file: Path): P[PReserved[T]] = P(P(r.token).map { _ => PReserved(r)(_) } ~~ !identContinues)./.pos
  implicit def reservedSym[$: P, T <: PSymbol](r: T)(implicit lineCol: LineCol, _file: Path): P[PReserved[T]] = P(r.token./ map { _ => PReserved(r)(_) }).pos

  class LeadingWhitespace[T](val p: () => P[T]) extends AnyVal {
    /**
      * Using `p.lw` is shorthand for `Pass ~ p` (the same parser but with possibly leading whitespace).
      *
      * A parser of the form `(p0 ~ p1.?).pos` or `(p0 ~ p2.rep).pos` may return an end position which
      * includes trailing whitespaces (incl. comments, newlines) if `p1` or `p2` fail to match (the `~` does this).
      * Instead we would like to use `(p0 ~~ (Pass ~ p1).?).pos` or `(p0 ~~ (Pass ~ p2).rep).pos`, which avoids this issue.
      */
    def lw[$: P]: LW[T] = new LW(() => Pass ~ p())
    def ~~~[$: P, V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R]): P[R] = (p() ~~ other.p()).asInstanceOf[P[R]]
    def ~~~/[$: P, V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R]): P[R] = (p() ~~/ other.p()).asInstanceOf[P[R]]
  }
  class PositionParsing[T](val p: () => P[((FilePosition, FilePosition)) => T]) extends AnyVal {
    def pos(implicit ctx: P[Any], lineCol: LineCol, _file: Path): P[T] = {
      // TODO: switch over to this?
      // Index ~~ p() ~~ Index map { case (start, f, end) => {
      //   val startPos = FilePosition(lineCol.getPos(start))
      //   val finishPos = FilePosition(lineCol.getPos(end))
      //   f((startPos, finishPos))
      // }}
      val startPos = FilePosition(lineCol.getPos(ctx.index))
      val res: P[((FilePosition, FilePosition)) => T] = p()
      val finishPos = FilePosition(lineCol.getPos(ctx.index))
      res.map(_((startPos, finishPos)))
    }
  }

  class ExtendedParsing[T](val p: () => P[T]) extends AnyVal {
    /** `(`...`)` */
    def parens[$: P](implicit lineCol: LineCol, _file: Path) = P((P(PSym.LParen) ~ p() ~ PSym.RParen) map (PGrouped.apply[PSym.Paren, T] _).tupled).pos
    /** `<`...`>` */
    def angles[$: P](implicit lineCol: LineCol, _file: Path) = P((P(PSym.LAngle) ~ p() ~ PSym.RAngle) map (PGrouped.apply[PSym.Angle, T] _).tupled).pos
    /** `"`...`"` */
    def quotes[$: P](implicit lineCol: LineCol, _file: Path) = P((P(PSym.Quote) ~ p() ~ PSym.Quote) map (PGrouped.apply[PSym.Quote.type, T] _).tupled).pos
    /** `{`...`}` */
    def braces[$: P](implicit lineCol: LineCol, _file: Path) = P((P(PSym.LBrace) ~ p() ~ PSym.RBrace) map (PGrouped.apply[PSym.Brace, T] _).tupled).pos
    /** `[`...`]` */
    def brackets[$: P](implicit lineCol: LineCol, _file: Path) = P((P(PSym.LBracket) ~ p() ~ PSym.RBracket) map (PGrouped.apply[PSym.Bracket, T] _).tupled).pos

    def delimited[$: P, U](sep: => P[U], min: Int = 0, max: Int = Int.MaxValue, exactly: Int = -1)(implicit lineCol: LineCol, _file: Path): P[PDelimited[T, U]] = P(
       (    (p() ~ Pass)./.lw.?.filter(p => (p.isEmpty && min <= 0 && exactly <= 0) || (!p.isEmpty && max > 0 && exactly != 0)) // Parse first element
        ~~~ (sep ~ p()).lw.rep(min = if (min == 0) 0 else min - 1, max = max - 1, exactly = if (exactly == -1) -1 else exactly - 1) // Parse other elements
        )
        .filter(p => p._1.isDefined || p._2.isEmpty) // Cannot start with delimiter
        .map { case (first, inner) => PDelimited(first, inner, None)(_) }
    ).pos

    def delimitedTrailing[$: P, U](sep: => P[U], min: Int = 0, max: Int = Int.MaxValue, exactly: Int = -1)(implicit lineCol: LineCol, _file: Path): P[PDelimited[T, Option[U]]] =
      P((p().lw ~~~ sep.lw.?./).repX(min = min, max = max, exactly = exactly)
        .map(seq => {
          val (ts, us) = seq.unzip
          PDelimited(ts.headOption, us.zip(ts.drop(1)), us.lastOption)(_)
        })
      ).pos
  }

  /**
    * A parser which matches leading whitespaces. See `LeadingWhitespace.lw` for more info. Can only be operated on in
    * restricted ways (e.g. `?`, `rep`, `|` or `map`), requiring that it is eventually appended to a normal parser (of type `P[V]`).
    *
    * For example, the following two are equivalent:
    * {{{("hello" ~~~ "world".lw.?).pos
    * ("hello" ~~ (Pass ~ "world").?).pos}}}
    * The type system prevents one from erroneously writing:
    * {{{("hello" ~ "world".lw.?).pos}}}
    */
  class LW[T](val p: () => P[T]) {
    def ?[V](implicit optioner: Implicits.Optioner[T, V], ctx: P[Any]): LW[V] = new LW(() => p().?.asInstanceOf[P[V]])
    def /(implicit ctx: P[Any]): LW[T] = new LW(() => p()./.asInstanceOf[P[T]])
    def rep[V](min: Int = 0, sep: => P[_] = null, max: Int = Int.MaxValue, exactly: Int = -1)(implicit repeater: Implicits.Repeater[T, V], ctx: P[Any]): LW[V] = new LW(() => p().rep(min, sep, max, exactly).asInstanceOf[P[V]])
    def rep[V](implicit repeater: Implicits.Repeater[T, V], ctx: P[Any]): LW[V] = this.rep()
    def |[V >: T](other: LW[V])(implicit ctx: P[Any]): LW[V] = new LW(() => (p() | other.p()).asInstanceOf[P[V]])
    def filter[V](f: T => Boolean)(implicit ctx: P[Any]): LW[T] = new LW(() => p().filter(f))
    def map[V](f: T => V): LW[V] = new LW(() => p().map(f))
    def ~~[V, R](other: => P[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~ other).asInstanceOf[P[R]]
    def ~~/[V, R](other: => P[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~/ other).asInstanceOf[P[R]]
    def ~~~[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~ other.p()).asInstanceOf[P[R]]
    def ~~~/[V, R](other: LW[V])(implicit s: Implicits.Sequencer[T, V, R], ctx: P[Any]): P[R] = (p() ~~/ other.p()).asInstanceOf[P[R]]
  }

  val basicKeywords: Set[PKeyword] = immutable.Set(PKw.Result,
    // types
    PKw.Int, PKw.Perm, PKw.Bool, PKw.Ref, PKw.Rational,
    // boolean constants
    PKw.True, PKw.False,
    // null
    PKw.Null,
    // preamble importing
    PKw.Import,
    // declaration keywords
    PKw.Method, PKw.Function, PKw.Predicate, PKw.Domain, PKw.Axiom, PKw.Var, PKw.Returns, PKw.Field, PKw.Define, PKw.Interpretation,
    // specifications
    PKw.Requires, PKw.Ensures, PKw.Invariant,
    // statements
    PKw.Fold, PKw.Unfold, PKw.Inhale, PKw.Exhale, PKw.New, PKw.Assert, PKw.Assume, PKw.Package, PKw.Apply, PKw.Quasihavoc, PKw.Quasihavocall,
    // control flow
    PKw.While, PKw.If, PKw.Elseif, PKw.Else, PKw.Goto, PKw.Label,
    // sequences
    PKw.Seq,
    // sets and multisets
    PKw.Set, PKw.Multiset, PKwOp.Union, PKwOp.Intersection, PKwOp.Setminus, PKwOp.Subset,
    // maps
    PKw.Map, PKwOp.Range, PKwOp.Domain,
    // prover hint expressions
    PKwOp.Unfolding, PKwOp.In, PKwOp.Applying,
    // old expression
    PKwOp.Old, PKw.Lhs,
    // other expressions
    PKwOp.Let,
    // quantification
    PKw.Forall, PKw.Exists, PKw.Forperm,
    // permission syntax
    PKwOp.Acc, PKw.Wildcard, PKw.Write, PKw.None, PKw.Epsilon, PKw.Perm,
    // modifiers
    PKw.Unique
  )
}

class FastParser {
  def parse(s: String, f: Path, plugins: Option[SilverPluginManager] = None, loader: FileLoader = DiskLoader) = {
    // Strategy to handle imports
    // Idea: Import every import reference and merge imported methods, functions, imports, .. into current program
    //       iterate until no new imports are present.
    //       To import each file at most once the absolute path is normalized (removes redundancies).
    //       For standard import the path relative to the import folder (in resources) is normalized and used.
    //       (normalize a path is a purely syntactic operation. if sally were a symbolic link removing sally/.. might
    //       result in a path that no longer locates the intended file. toRealPath() might be an alternative)

    val file = f.toAbsolutePath().normalize()
    val data = ParserData(plugins, loader, mutable.HashSet(file))
    val program = RecParser(file, data, false).parses(s)
    MacroExpander.expandDefines(program)
  }

  case class ParserData(plugins: Option[SilverPluginManager], loader: FileLoader, local: mutable.HashSet[Path], std: mutable.HashSet[Path] = mutable.HashSet.empty)

  case class RecParser(file: Path, data: ParserData, isStd: Boolean) {

    def parses(s: String): PProgram = {
      val program = parseFile(file, s)

      val imported = program.imports.flatMap(ip => {
        // Normalize the path
        val importPath =
          if (ip.local) file.resolveSibling(ip.file.str).normalize()
          else Paths.get(ip.file.str).normalize()
        // Do the import
        if (ip.local && !isStd) {
          if (data.local.add(importPath)) {
            ip.resolved = Some(importPath)
            Some(importLocal(importPath, ip, data))
          } else {
            None
          }
        } else {
          // if `ip.local && isStd` local import get transformed to standard imports
          if (data.std.add(importPath)) {
            ip.resolved = Some(importPath)
            ip.local = false
            Some(importStandard(importPath, ip, data))
          } else {
            None
          }
        }
      })
      program.newImported(imported)
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
  def importProgram(imported_source: String, path: Path, importStmt: PImport, data: ParserData, isStd: Boolean): PProgram = {

    val transformed_source = if (data.plugins.isDefined){
      data.plugins.get.beforeParse(imported_source, isImported = true) match {
        case Some(transformed) => transformed
        case None =>
          val pos = SourcePosition(importStmt.pos._1.file, importStmt.pos._1, importStmt.pos._2)
          return PProgram.error(ParseError(s"Plugin failed: ${data.plugins.get.errors.map(_.toString).mkString(", ")}", pos))
      }
    } else {
      imported_source
    }
    RecParser(path, data, isStd).parses(transformed_source)
  }

  /**
    * Opens (and closes) standard file to be imported, parses it and converts it into a program.
    * Standard files are located in the resources inside a "import" folder.
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importStandard(path: Path, importStmt: PImport, data: ParserData): PProgram = {
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
            val pos = SourcePosition(importStmt.pos._1.file, importStmt.pos._1, importStmt.pos._2)
            return PProgram.error(ParseError(s"could not import file ($e)", pos))
        } finally {
          source.close()
        }
      } catch {
        case _: java.lang.NullPointerException =>
          val pos = SourcePosition(importStmt.pos._1.file, importStmt.pos._1, importStmt.pos._2)
          return PProgram.error(ParseError(s"file <$path> does not exist", pos))
        case e@(_: RuntimeException | _: java.io.IOException) =>
          val pos = SourcePosition(importStmt.pos._1.file, importStmt.pos._1, importStmt.pos._2)
          return PProgram.error(ParseError(s"could not import file ($e)", pos))
      }
    val imported_source = buffer.mkString("\n") + "\n"
    importProgram(imported_source, path, importStmt, data, true)
  }

  /**
    * Opens (and closes) local file to be imported, parses it and converts it into a program.
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importLocal(path: Path, importStmt: PImport, data: ParserData): PProgram = {
    data.loader.loadContent(path) match {
      case Failure(exception) =>
        val pos = SourcePosition(importStmt.pos._1.file, importStmt.pos._1, importStmt.pos._2)
        return PProgram.error(ParseError(s"could not import file ($exception)", pos))
      case Success(value) => importProgram(value, path, importStmt, data, false)
    }
  }

  //////////////////////////
  // Actual Parser starts from here
  //////////////////////////

  import fastparse._
  import FastParserCompanion.{ExtendedParsing, identContinues, identStarts, LeadingWhitespace, Pos, PositionParsing, reservedKw, reservedSym}


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

  lazy val keywords: Set[String] = (FastParserCompanion.basicKeywords | ParserExtension.extendedKeywords).map(_.keyword)

  def reservedSymMany[$: P, T <: PSymbol](clashes: => Option[P[_]], s: => P[_], f: String => T): P[PReserved[T]] =
    P(!clashes.getOrElse(Fail) ~~ s.!./.map { op => PReserved(f(op))(_) }).pos

  /**
    * Parses one of many possible reserved words, should only be used with
    * `StringIn` as `s`. The parser given in `f` should be mostly
    * pre-initialized (e.g. from a `def`), see
    * [here](https://com-lihaoyi.github.io/fastparse/#FlatMap). If only a single
    * reserved word is to be parsed, use `reservedKw` instead.
    */
  def reservedKwMany[$: P, U](s: => P[_], f: String => Pos => P[U]): P[U] = {
    def parser = (s.! ~~ !identContinues)./.map(s => { p: Pos => (s, p) }).pos
    parser.flatMapX { case (s, p) => Pass ~ f(s)(p) }
  }

  /** `(`...`,` ...`,` ...`)` */
  def argList[$: P, T](p: => P[T]) = p.delimited(PSym.Comma).parens

  /** `[`...`,` ...`,` ...`]` */
  def typeList[$: P, T](p: => P[T]) = p.delimited(PSym.Comma).brackets

  /** ...`;`? ...`;`? ...`;`? */
  def semiSeparated[$: P, T](p: => P[T]) = p.delimitedTrailing(PSym.Semi)

  def foldPExp[E <: PExp](e: E, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) => a(t) }

  def atomReservedKw[$: P]: P[PExp] = {
    reservedKwMany(
      StringIn("true", "false", "null", "old", "result", "acc", "none", "wildcard", "write", "epsilon", "perm", "let", "forall", "exists", "forperm",
        "unfolding", "applying", "inhaling", "Set", "Seq", "Multiset", "Map", "range", "domain", "new"),
      str => pos => str match {
        case "true" => Pass.map(_ => PBoolLit(PReserved(PKw.True)(pos))(_))
        case "false" => Pass.map(_ => PBoolLit(PReserved(PKw.False)(pos))(_))
        case "null" => Pass.map(_ => PNullLit(PReserved(PKw.Null)(pos))(_))
        case "old" => old.map(_(PReserved(PKwOp.Old)(pos)))
        case "result" => Pass.map(_ => PResultLit(PReserved(PKw.Result)(pos))(_))
        case "acc" => accessPredImpl.map(_(PReserved(PKwOp.Acc)(pos)))
        case "none" => Pass.map(_ => PNoPerm(PReserved(PKw.None)(pos))(_))
        case "wildcard" => Pass.map(_ => PWildcard(PReserved(PKw.Wildcard)(pos))(_))
        case "write" => Pass.map(_ => PFullPerm(PReserved(PKw.Write)(pos))(_))
        case "epsilon" => Pass.map(_ => PEpsilon(PReserved(PKw.Epsilon)(pos))(_))
        case "perm" => perm.map(_(PReserved(PKwOp.Perm)(pos)))
        case "let" => let.map(_(PReserved(PKwOp.Let)(pos)))
        case "forall" => forall.map(_(PReserved(PKw.Forall)(pos)))
        case "exists" => exists.map(_(PReserved(PKw.Exists)(pos)))
        case "forperm" => forperm.map(_(PReserved(PKw.Forperm)(pos)))
        case "unfolding" => unfolding.map(_(PReserved(PKwOp.Unfolding)(pos)))
        case "applying" => applying.map(_(PReserved(PKwOp.Applying)(pos)))
        case "inhaling" => inhaling.map(_(PReserved(PKwOp.Inhaling)(pos)))
        case "Set" => setConstructor.map(_(PReserved(PKwOp.Set)(pos)))
        case "Seq" => seqConstructor.map(_(PReserved(PKwOp.Seq)(pos)))
        case "Multiset" => multisetConstructor.map(_(PReserved(PKwOp.Multiset)(pos)))
        case "Map" => mapConstructor.map(_(PReserved(PKwOp.Map)(pos)))
        case "range" => mapRange.map(_(PReserved(PKwOp.Range)(pos)))
        case "domain" => mapDomain.map(_(PReserved(PKwOp.Domain)(pos)))
        case "new" => newExp.map(_(PReserved(PKw.New)(pos)))
      }
    ).pos
  }

  def atom(bracketed: Boolean = false)(implicit ctx : P[_]) : P[PExp] = P(ParserExtension.newExpAtStart(ctx) | annotatedAtom
    | atomReservedKw | integer | unExp | size | lbracketExp
    | maybeTypedFuncApp(bracketed) | idnuse | ParserExtension.newExpAtEnd(ctx))

  def atomParen[$: P](bracketed: Boolean = false): P[PExp] = P(expParen(true).parens.map{ g => g.inner.brackets = Some(g); g.inner } | atom(bracketed))

  def stringLiteral[$: P]: P[PStringLiteral] = P((CharsWhile(_ != '\"').! map PRawString.apply).pos.quotes map (PStringLiteral.apply _)).pos

  def annotation[$: P]: P[PAnnotation] = P((P(PSym.At) ~~ annotationIdentifier ~ argList(stringLiteral)) map (PAnnotation.apply _).tupled).pos

  def annotated[$: P, T](inner: => P[PAnnotationsPosition => T]): P[T] = P((annotation.rep(0) ~ inner).map {
    case (annotations, i) => pos: Pos => i(PAnnotationsPosition(annotations, pos))
  }).pos

  def annotatedAtom[$: P]: P[PExp] = P((annotation ~ atomParen()) map (PAnnotatedExp.apply _).tupled).pos

  def result[$: P]: P[PResultLit] = P(P(PKw.Result) map (PResultLit.apply _)).pos

  def unExp[$: P]: P[PUnExp] = P(((P(PSymOp.Neg) | PSymOp.Not) ~ suffixExpr()) map (PUnExp.apply _).tupled).pos

  def strInteger[$: P]: P[String] = P(CharIn("0-9").repX(1).!./)

  def integer[$: P]: P[PIntLit] = P((strInteger) map { s => PIntLit(BigInt(s))(_) }).pos

  def identifier[$: P]: P[Unit] = identStarts ~~ identContinues.repX

  def annotationIdentifier[$: P]: P[PRawString] = P((identStarts ~~ CharIn("0-9", "A-Z", "a-z", "$_.").repX).!./ map PRawString.apply).pos

  def ident[$: P]: P[String] = identifier.!.filter(a => !keywords.contains(a)).opaque("identifier")

  def idnuse[$: P]: P[PIdnUseExp] = P(ident map (PIdnUseExp.apply _)).pos

  def idnref[$: P, T <: PDeclarationInner](implicit ctag: scala.reflect.ClassTag[T]): P[PIdnRef[T]] = P(ident map (PIdnRef.apply[T] _)).pos

  def oldLabel[$: P]: P[Either[PKw.Lhs, PIdnRef[PLabel]]] = P((P(PKw.Lhs) map (Left(_))) | (idnref[$, PLabel] map (Right(_))))

  def old[$: P]: P[PKwOp.Old => Pos => POldExp] = P(oldLabel.brackets.? ~ exp.parens).map {
    case (lbl, g) => POldExp(_, lbl, g)
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
  def parenthesizedExp[$: P]: P[PGrouped.Paren[PExp]] = exp.parens

  def indexSuffix[$: P]: P[(PSymOp.LBracket, PExp, PSymOp.RBracket) => Pos => SuffixedExpressionGenerator[PExp]] = P(
    (P(PSymOp.Assign) ~ exp).map { case (a, v) => (l: PSymOp.LBracket, i: PExp, r: PSymOp.RBracket) => pos: Pos
      => SuffixedExpressionGenerator[PExp](e => PUpdate(e, l, i, a, v, r)(e.pos._1, pos._2)) } |
    (P(PSymOp.DotDot) ~ exp.?).map { case (d, m) => (l: PSymOp.LBracket, n: PExp, r: PSymOp.RBracket) => pos: Pos
      => SuffixedExpressionGenerator[PExp](e => PSeqSlice(e, l, Some(n), d, m, r)(e.pos._1, pos._2)) } |
    Pass.map { _ => (l: PSymOp.LBracket, e1: PExp, r: PSymOp.RBracket) => pos: Pos
      => SuffixedExpressionGenerator[PExp](e0 => PLookup(e0, l, e1, r)(e0.pos._1, pos._2)) })

  def fieldAccess[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(((!P(PSymOp.DotDot) ~~ PSymOp.Dot) ~ idnref[$, PFieldDecl]) map { case (dot, id) => pos: Pos => SuffixedExpressionGenerator[PExp](e => PFieldAccess(e, dot, id)(e.pos._1, pos._2)) }).pos

  def sliceEnd[$: P]: P[((PSymOp.LBracket, PSymOp.RBracket)) => Pos => SuffixedExpressionGenerator[PExp]] =
    P((P(PSymOp.DotDot) ~ exp).map { case (d, n) => b => pos: Pos
          => SuffixedExpressionGenerator[PExp](e => PSeqSlice(e, b._1, None, d, Some(n), b._2)(e.pos._1, pos._2)) })

  def indexContinue[$: P]: P[((PSymOp.LBracket, PSymOp.RBracket)) => Pos => SuffixedExpressionGenerator[PExp]] =
    P((exp ~ indexSuffix).map { case (e, s) => b => s(b._1, e, b._2) })

  def index[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P((P(PSymOp.LBracket) ~ (sliceEnd | indexContinue) ~ PSymOp.RBracket) map { case (l, f, r) => f(l, r) }).pos

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
    case "union" => Pass.map(_ => PReserved(PKwOp.Union)(_))
    case "intersection" => Pass.map(_ => PReserved(PKwOp.Intersection)(_))
    case "setminus" => Pass.map(_ => PReserved(PKwOp.Setminus)(_))
    case "subset" => Pass.map(_ => PReserved(PKwOp.Subset)(_))
  }).pos)

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
        PBinExp(left, PReserved(PSymOp.AndAnd)(NoPosition, NoPosition), PBinExp(middle.deepCopyAll.asInstanceOf[PExp], op, right)(middle.pos._1, pos._2))(left.pos._1, pos._2)
      case left@PBinExp(_, PReserved(PSymOp.AndAnd), PBinExp(_, op0, middle)) if cmpOps.contains(op0.rs.token) && left != from =>
        PBinExp(left, PReserved(PSymOp.AndAnd)(NoPosition, NoPosition), PBinExp(middle.deepCopyAll.asInstanceOf[PExp], op, right)(middle.pos._1, pos._2))(left.pos._1, pos._2)
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

  def accessPredImpl[$: P]: P[PKwOp.Acc => Pos => PAccPred] = P(maybePairArgument(locAcc, exp).parens map { arg => PAccPred(_, arg) })

  def accessPred[$: P]: P[PAccPred] = P((P(PKwOp.Acc) ~ accessPredImpl) map { case (k, f) => f(k) }).pos

  def resAcc[$: P]: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  def locAcc[$: P]: P[PLocationAccess] = P(fieldAcc | predAcc)

  def fieldAcc[$: P]: P[PFieldAccess] =
    P(NoCut(suffixExpr()) flatMap {
      case fa: PFieldAccess => Pass.map(_ => fa)
      case _ => Fail
    })

  def predAcc[$: P]: P[PCall] = funcApp

  def perm[$: P]: P[PKwOp.Perm => Pos => PCurPerm] = P(resAcc.parens map { r => PCurPerm(_, r) })

  def let[$: P]: P[PKwOp.Let => Pos => PExp] =
    P(idndef ~ PSymOp.EqEq ~ parenthesizedExp ~ PKwOp.In ~ exp).map {
      case (id, eq, exp1, in, exp2) =>
        val nestedScope = PLetNestedScope(exp2)(exp2.pos)
        k => PLet(k, id, eq, exp1, in, nestedScope)(_)
    }

  def idndef[$: P]: P[PIdnDef] = P(ident map (PIdnDef.apply _)).pos

  def forall[$: P]: P[PKw.Forall => Pos => PExp] = P(nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ PSym.ColonColon ~ trigger.rep ~ exp).map {
    case (a, o, b, c) => PForall(_, a, o, b, c)
  }
  def exists[$: P]: P[PKw.Exists => Pos => PExp] = P(nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ PSym.ColonColon ~ trigger.rep ~ exp).map {
    case (a, o, b, c) => PExists(_, a, o, b, c)
  }

  def nonEmptyIdnTypeList[$: P, T](f: PIdnTypeBinding => T): P[PDelimited[T, PSym.Comma]] = P((idnTypeBinding map f).delimited(PSym.Comma, min = 1))

  def idnTypeBinding[$: P]: P[PIdnTypeBinding] = P((idndef ~ PSym.Colon ~ typ) map (PIdnTypeBinding.apply _).tupled).pos

  def typReservedKw[$: P]: P[PType] = {
    reservedKwMany(
      StringIn("Rational", "Int", "Bool", "Perm", "Ref", "Seq", "Set", "Multiset", "Map"),
      str => pos => str match {
        case "Rational" => Pass.map { _ =>
            val p = pos.asInstanceOf[(HasLineColumn, HasLineColumn)]
            _warnings = _warnings :+ ParseWarning("Rational is deprecated, use Perm instead", SourcePosition(_file, p._1, p._2))
            PPrimitiv(PReserved(PKw.Rational)(pos))(_)
          }
        case "Int" => Pass.map(_ => PPrimitiv(PReserved(PKw.Int)(pos))(_))
        case "Bool" => Pass.map(_ => PPrimitiv(PReserved(PKw.Bool)(pos))(_))
        case "Perm" => Pass.map(_ => PPrimitiv(PReserved(PKw.Perm)(pos))(_))
        case "Ref" => Pass.map(_ => PPrimitiv(PReserved(PKw.Ref)(pos))(_))
        case "Seq" => seqType.map(_(PReserved(PKw.Seq)(pos)))
        case "Set" => setType.map(_(PReserved(PKw.Set)(pos)))
        case "Multiset" => multisetType.map(_(PReserved(PKw.Multiset)(pos)))
        case "Map" => mapType.map(_(PReserved(PKw.Map)(pos)))
      }
    ).pos
  }

  def typ[$: P]: P[PType] = P(typReservedKw | domainTyp | macroType)

  def domainTyp[$: P]: P[PDomainType] = P((idnref[$, PTypeDeclaration] ~~~ typeList(typ).lw.?) map (PDomainType.apply _).tupled).pos

  def seqType[$: P]: P[PKw.Seq => Pos => PSeqType] = P(typ.brackets map { t => PSeqType(_, t) })

  def setType[$: P]: P[PKw.Set => Pos => PSetType] = P(typ.brackets map { t => PSetType(_, t) })

  def multisetType[$: P]: P[PKw.Multiset => Pos => PMultisetType] = P(typ.brackets map { t => PMultisetType(_, t) })

  def mapType[$: P]: P[PKw.Map => Pos => PMapType] = P(pairArgument(typ, typ).brackets map { t => PMapType(_, t)})

  /** Only for call-like macros, `idnuse`-like ones are parsed by `domainTyp`. */
  def macroType[$: P] : P[PMacroType] = funcApp.map(PMacroType(_))

  def trigger[$: P]: P[PTrigger] = P(exp.delimited(PSym.Comma).braces map (PTrigger.apply _)).pos

  def forperm[$: P]: P[PKw.Forperm => Pos => PExp] = P(nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ resAcc.brackets ~ PSym.ColonColon ~ exp).map {
    case (args, res, op, body) => PForPerm(_, args, res, op, body)
  }

  def unfolding[$: P]: P[PKwOp.Unfolding => Pos => PExp] = P(predicateAccessAssertion ~ PKwOp.In ~ exp).map {
    case (a, in, b) => PUnfolding(_, a, in, b)
  }

  def applying[$: P]: P[PKwOp.Applying => Pos => PExp] = P(magicWandExp().parens ~ PKwOp.In ~ exp).map {
    case (wand, op, b) =>
      wand.inner.brackets = Some(wand)
      PApplying(_, wand.inner, op, b)
  }

  def inhaling[$: P]: P[PKwOp.Inhaling => Pos => PExp] = P(exp.parens ~ PKwOp.In ~ exp).map {
    case (exp, in, body) => PInhaling(_, exp.inner, in, body)
  }

  def predicateAccessAssertion[$: P]: P[PAccAssertion] = P(accessPred | predAcc)

  def setConstructor[$: P]: P[PKwOp.Set => Pos => PExp] =
    builtinConstructor(typ, exp)(
      { case (t, g) => PEmptySet(_, t, g) },
      { t => PExplicitSet(_, t) }
    )

  def seqConstructor[$: P]: P[PKwOp.Seq => Pos => PExp] =
    builtinConstructor(typ, exp)(
      { case (t, g) => PEmptySeq(_, t, g) },
      { t => PExplicitSeq(_, t) }
    )

  def multisetConstructor[$: P]: P[PKwOp.Multiset => Pos => PExp] =
    builtinConstructor(typ, exp)(
      { case (t, g) => PEmptyMultiset(_, t, g) },
      { t => PExplicitMultiset(_, t) }
    )

  def mapConstructor[$: P]: P[PKwOp.Map => Pos => PExp] =
    builtinConstructor(pairArgument(typ, typ), maplet)(
      { case (t, g) => PEmptyMap(_, t, g) },
      { t => PExplicitMap(_, t) }
    )

  def builtinConstructor[$: P, T, U, E <: PNode](types: => P[T], element: => P[E])(
    empty: (Option[PGrouped[PSym.Bracket, T]], PDelimited.Comma[PSym.Paren, Nothing]) => U,
    nonEmpty: (PDelimited.Comma[PSym.Paren, E]) => U
  ): P[U] = P((types.brackets.lw.? ~~ argList(element))
    filter { case (t, es) => es.inner.length == 0 || t.isEmpty }
    map {
      case (t, es) if es.inner.length == 0 => empty(t, es.update(Nil))
      case (_, es) => nonEmpty(es)
    })

  def lbracketExp[$: P]: P[PExp] = P((P(PSymOp.LBracket) ~ NoCut(exp) ~ (inhaleExhale | seqRange)) map {
    case (l, e, op) => op(l, e)
  }).pos

  def inhaleExhale[$: P]: P[(PSymOp.LBracket, PExp) => Pos => PInhaleExhaleExp] = P((P(PSymOp.Comma) ~ exp ~ PSymOp.RBracket) map {
    case (c, rhs, rb) => (lb, lhs) => PInhaleExhaleExp(lb, lhs, c, rhs, rb)(_)
  })

  def seqRange[$: P]: P[(PSymOp.LBracket, PExp) => Pos => PRangeSeq] = P((P(PSymOp.DotDot) ~ exp ~ PSymOp.RParen) map {
    case (dd, rhs, rb) => (lb, lhs) => PRangeSeq(lb, lhs, dd, rhs, rb)(_)
  })

  def size[$: P]: P[PExp] = P((P(PSymOp.Or) ~ exp ~ PSymOp.Or) map (PSize.apply _).tupled).pos

  def maplet[$: P]: P[PMaplet] = P((exp ~ PSymOp.Assign ~ exp) map (PMaplet.apply _).tupled).pos

  def mapDomain[$: P]: P[PKwOp.Domain => Pos => PMapDomain] = P(exp.parens map { e => PMapDomain(_, e) })

  def mapRange[$: P]: P[PKwOp.Range => Pos => PMapRange] = P(exp.parens map { e => PMapRange(_, e) })

  def newExp[$: P]: P[PKw.New => Pos => PNewExp] = P(newExpFields.parens map { n => PNewExp(_, n) })

  def newExpFields[$: P]: P[Either[PSym.Star, PDelimited[PIdnRef[PFieldDecl], PSym.Comma]]] = P(P(PSym.Star).map(Left(_)) | P(idnref[$, PFieldDecl].delimited(PSym.Comma).map(Right(_))))

  def funcApp[$: P]: P[PCall] = P(idnref[$, PCallable] ~~ " ".repX(1).map { _ => pos: Pos => pos }.pos.? ~~ argList(exp)).map {
    case (func, space, args) =>
      space.foreach { space =>
        _warnings = _warnings :+ ParseWarning("Whitespace between a function identifier and the opening paren is deprecated, remove the spaces", SourcePosition(_file, space._1, space._2))
      }
      PCall(func, args, None)(_)
  }.pos

  def maybeTypedFuncApp[$: P](bracketed: Boolean): P[PCall] = P(if (!bracketed) funcApp else (funcApp ~~~ (P(PSym.Colon) ~ typ).lw.?).map {
    case (func, typeGiven) => func.copy(typeAnnotated = typeGiven)(_)
  }.pos)

  def stmtReservedKw[$: P](allowDefine: Boolean): P[PStmt] = {
    reservedKwMany(
      StringIn("fold", "unfold", "exhale", "assert", "inhale", "assume", "if", "while", "var", "define",
        "goto", "label", "package", "apply", "quasihavoc", "quasihavocall"),
      str => pos => str match {
        case "fold" => fold.map(_(PReserved(PKw.Fold)(pos)))
        case "unfold" => unfold.map(_(PReserved(PKw.Unfold)(pos)))
        case "exhale" => exhale.map(_(PReserved(PKw.Exhale)(pos)))
        case "assert" => assertStmt.map(_(PReserved(PKw.Assert)(pos)))
        case "inhale" => inhale.map(_(PReserved(PKw.Inhale)(pos)))
        case "assume" => assume.map(_(PReserved(PKw.Assume)(pos)))
        case "if" => ifThenElse.map(_(PReserved(PKw.If)(pos)))
        case "while" => whileStmt.map(_(PReserved(PKw.While)(pos)))
        case "var" => localVars.map(_(PReserved(PKw.Var)(pos)))
        case "define" if allowDefine => defineDeclStmt.map(_(PReserved(PKw.Define)(pos)))
        case "define" if !allowDefine => Fail
        case "goto" => goto.map(_(PReserved(PKw.Goto)(pos)))
        case "label" => label.map(_(PReserved(PKw.Label)(pos)))
        case "package" => packageWand.map(_(PReserved(PKw.Package)(pos)))
        case "apply" => applyWand.map(_(PReserved(PKw.Apply)(pos)))
        case "quasihavoc" => quasihavoc.map(_(PReserved(PKw.Quasihavoc)(pos)))
        case "quasihavocall" => quasihavocall.map(_(PReserved(PKw.Quasihavocall)(pos)))
      }
    ).pos
  }

  def stmt(allowDefine: Boolean = true)(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | annotatedStmt |
    stmtReservedKw(allowDefine) | stmtBlock(allowDefine) |
    assign | ParserExtension.newStmtAtEnd(ctx))

  def annotatedStmt(implicit ctx : P[_]): P[PStmt] = P((annotation ~ stmt()) map (PAnnotatedStmt.apply _).tupled).pos

  def assignTarget[$: P]: P[PExp with PAssignTarget] = P(fieldAcc | funcApp | idnuse)

  // Parses any of `idn`, `idn(args)` or `... := exp` (where `...` is a comma
  // delimited sequence of field access, function application or identifier)
  def assign[$: P]: P[PAssign] = P(
    (assignTarget.delimited(PSym.Comma, min = 1) ~~~ (P(PSymOp.Assign).map(Some(_)) ~ exp).lw.?)
      filter (a => a._2.isDefined || (a._1.length == 1 && (a._1.head.isInstanceOf[PIdnUse] || a._1.head.isInstanceOf[PCall])))
      map (a => if (a._2.isDefined) PAssign(a._1, a._2.get._1, a._2.get._2) _ else PAssign(PDelimited.empty, None, a._1.head) _)
    ).pos

  def fold[$: P]: P[PKw.Fold => Pos => PFold] =
    P(predicateAccessAssertion map { e => PFold(_, e) })

  def unfold[$: P]: P[PKw.Unfold => Pos => PUnfold] =
    P(predicateAccessAssertion map { e => PUnfold(_, e) })

  def exhale[$: P]: P[PKw.Exhale => Pos => PExhale] = P(exp map { e => PExhale(_, e) })

  def assertStmt[$: P]: P[PKw.Assert => Pos => PAssert] = P(exp map { e => PAssert(_, e) })

  def inhale[$: P]: P[PKw.Inhale => Pos => PInhale] = P(exp map { e => PInhale(_, e) })

  def assume[$: P]: P[PKw.Assume => Pos => PAssume] = P(exp map { e => PAssume(_, e) })

  // Parsing Havoc statements
  // Havoc statements have two forms:
  // in the grammar. Note that it is still possible to express "(<exp1> ==> <exp2>) ==> <resource>
  // using parentheses.

  // Havocall follows a similar pattern to havoc but allows quantifying over variables.

  def quasihavoc[$: P]: P[PKw.Quasihavoc => Pos => PQuasihavoc] =
    P(((NoCut(magicWandExp()) ~ PSymOp.Implies).? ~ exp) map { case (lhs, rhs) => PQuasihavoc(_, lhs, rhs) })

  def quasihavocall[$: P]: P[PKw.Quasihavocall => Pos => PQuasihavocall] =
    P((nonEmptyIdnTypeList(PLogicalVarDecl(_)) ~ PSym.ColonColon ~ (NoCut(magicWandExp()) ~ PSymOp.Implies).? ~ exp)
      map { case (args, c, lhs, rhs) => PQuasihavocall(_, args, c, lhs, rhs) _ })

  def ifThenElse[$: P]: P[PKw.If => Pos => PIf] =
    P((parenthesizedExp ~ stmtBlock() ~~~ elseIfOrElse.lw.?) map { case (cond, thn, els) => PIf(_, cond, thn, els) })

  def stmtBlock[$: P](allowDefine: Boolean = true): P[PSeqn] =  P(semiSeparated(stmt(allowDefine)).braces map (PSeqn.apply _)).pos

  def elseIfOrElse[$: P]: P[PIfContinuation] = elseIf | elseBlock

  def elseIf[$: P]: P[PIf] = P((P(PKw.Elseif) ~ parenthesizedExp ~ stmtBlock() ~~~ elseIfOrElse.lw.?) map (PIf.apply _).tupled).pos

  def elseBlock[$: P]: P[PElse] =
    P((P(PKw.Else) ~ stmtBlock()) map (PElse.apply _).tupled).pos

  def whileStmt[$: P]: P[PKw.While => Pos => PWhile] =
    P((parenthesizedExp ~~ semiSeparated(invariant) ~ stmtBlock()) map { case (cond, invs, body) => PWhile(_, cond, invs, body) })

  def invariant(implicit ctx : P[_]) : P[PSpecification[PKw.InvSpec]] = P((P(PKw.Invariant) ~ exp).map((PSpecification.apply _).tupled).pos | ParserExtension.invSpecification(ctx))

  def localVars[$: P]: P[PKw.Var => Pos => PVars] =
    P((nonEmptyIdnTypeList(PLocalVarDecl(_)) ~~~ (P(PSymOp.Assign) ~ exp).lw.?) map { case (a, i) => PVars(_, a, i) })

  def defineDecl[$: P]: P[PKw.Define => PAnnotationsPosition => PDefine] =
    P((idndef ~~~/ NoCut(argList((idndef map PDefineParam.apply).pos)).lw.? ~ (stmtBlock(false) | exp)) map {
      case (idn, args, body) => k => ap: PAnnotationsPosition => PDefine(ap.annotations, k, idn, args, body)(ap.pos)
    })

  def defineDeclStmt[$: P]: P[PKw.Define => Pos => PDefine] = P(defineDecl.map { f => k => pos: Pos => f(k)(PAnnotationsPosition(Nil, pos)) })

  def goto[$: P]: P[PKw.Goto => Pos => PGoto] = P(idnref[$, PLabel] map { i => PGoto(_, i) _ })

  def label[$: P]: P[PKw.Label => Pos => PLabel] =
    P((idndef ~~ semiSeparated(invariant)) map { case (i, inv) => k=> PLabel(k, i, inv) _ })

  def packageWand[$: P]: P[PKw.Package => Pos => PPackageWand] =
    P((magicWandExp() ~~~ stmtBlock().lw.?) map { case (wand, proof) => PPackageWand(_, wand, proof) _ })

  def applyWand[$: P]: P[PKw.Apply => Pos => PApplyWand] =
    P(magicWandExp() map { wand => PApplyWand(_, wand) _ })

  def memberReservedKw[$: P]: P[PAnnotationsPosition => PMember] = {
    reservedKwMany(
      StringIn("import", "define", "field", "method", "domain", "function", "predicate"),
      str => pos => str match {
        case "import" => preambleImport.map(_(PReserved(PKw.Import)(pos)))
        case "define" => defineDecl.map(_(PReserved(PKw.Define)(pos)))
        case "field" => fieldDecl.map(_(PReserved(PKw.Field)(pos)))
        case "method" => methodDecl.map(_(PReserved(PKw.Method)(pos)))
        case "domain" => domainDecl.map(_(PReserved(PKw.Domain)(pos)))
        case "function" => functionDecl.map(_(PReserved(PKw.Function)(pos)))
        case "predicate" => predicateDecl.map(_(PReserved(PKw.Predicate)(pos)))
      }
    )
  }

  def programMember(implicit ctx : P[_]): P[PMember] =
    annotated(ParserExtension.newDeclAtStart(ctx) | memberReservedKw | ParserExtension.newDeclAtEnd(ctx))

  def programDecl[$: P]: P[PProgram] =
    P(programMember.rep map (members => {
      val warnings = _warnings
      _warnings = Seq()
      PProgram(Nil, members)(_, warnings)
    })).pos

  def preambleImport[$: P]: P[PKw.Import => PAnnotationsPosition => PImport] = P(
    (relativeFilePath.quotes.map { case s => pos: Pos => (true, PStringLiteral(s)(pos)) }
   | relativeFilePath.angles.map { case s => pos: Pos => (false, PStringLiteral(s)(pos)) }).pos
    map {
    case (local, filename) => k => ap: PAnnotationsPosition =>
      val i = PImport(ap.annotations, k, filename)(ap.pos)
      i.local = local
      i
  })

  def relativeFilePath[$: P]: P[PRawString] = ((CharIn("~.").? ~~ (CharIn("/").? ~~ CharIn(".", "A-Z", "a-z", "0-9", "_\\- \n\t")).rep(1)).! map PRawString.apply).pos

  def domainInterp[$: P]: P[PDomainInterpretation] = P((ident.map(PRawString.apply).pos ~ PSym.Colon ~ stringLiteral) map (PDomainInterpretation.apply _).tupled).pos
  def domainInterps[$: P]: P[PDomainInterpretations] =
    P((P(PKw.Interpretation) ~ argList(domainInterp)) map (PDomainInterpretations.apply _).tupled).pos

  def domainDecl[$: P]: P[PKw.Domain => PAnnotationsPosition => PDomain] = P(idndef ~~~ typeList(domainTypeVarDecl).lw.? ~~~ domainInterps.lw.? ~
    annotated(domainFunctionDecl | axiomDecl).rep.map(PDomainMembers1.apply _).pos.braces).map {
    case (name, typparams, interpretations, block) =>
      val members = block.inner.members
      val funcs1 = members collect { case m: PDomainFunction1 => m }
      val axioms1 = members collect { case m: PAxiom1 => m }
      val funcs = funcs1 map (f => (PDomainFunction(f.annotations, f.unique, f.function, f.idndef, f.args, f.c, f.typ, f.interpretation)(f.pos), f.s))
      val axioms = axioms1 map (a => (PAxiom(a.annotations, a.axiom, a.idndef, a.exp)(a.pos), a.s))
      val allMembers = block.update(PDomainMembers(PDelimited(funcs)(NoPosition, NoPosition), PDelimited(axioms)(NoPosition, NoPosition))(block.pos))
      k => ap: PAnnotationsPosition => PDomain(
        ap.annotations,
        k,
        name,
        typparams,
        interpretations,
        allMembers)(ap.pos)
  }

  def domainTypeVarDecl[$: P]: P[PTypeVarDecl] = P(idndef map (PTypeVarDecl.apply _)).pos

  def domainFunctionInterpretation[$: P]: P[PDomainFunctionInterpretation] = P((P(PKw.Interpretation) ~ stringLiteral) map (PDomainFunctionInterpretation.apply _).tupled).pos
  def domainFunctionDecl[$: P]: P[PAnnotationsPosition => PDomainFunction1] = P(P(PKw.Unique).? ~ domainFunctionSignature ~ domainFunctionInterpretation.? ~~~ P(PSym.Semi).lw.?).map {
    case (unique, (function, idn, args, c, typ), interpretation, s) => ap: PAnnotationsPosition => PDomainFunction1(ap.annotations, unique, function, idn, args, c, typ, interpretation, s)(ap.pos)
  }

  def domainFunctionSignature[$: P] = P(P(PKw.FunctionD) ~ idndef ~ argList(domainFunctionArg) ~ PSym.Colon ~ typ)

  def domainFunctionArg[$: P]: P[PDomainFunctionArg] = P(idnTypeBinding.map(PDomainFunctionArg(_)) | typ.map(PDomainFunctionArg(None, None, _) _).pos)

  def formalArg[$: P]: P[PFormalArgDecl] = P(idnTypeBinding map (PFormalArgDecl(_)))

  def bracedExp[$: P]: P[PBracedExp] = P(exp.braces map (PBracedExp(_) _)).pos

  def axiomDecl[$: P]: P[PAnnotationsPosition => PAxiom1] = P(P(PKw.Axiom) ~ idndef.? ~ bracedExp ~~~ P(PSym.Semi).lw.?).map { case (k, a, b, s) =>
    ap: PAnnotationsPosition => PAxiom1(ap.annotations, k, a, b, s)(ap.pos)
  }

  def fieldDecl[$: P]: P[PKw.Field => PAnnotationsPosition => PFields] = P((nonEmptyIdnTypeList(PFieldDecl(_)) ~~~ P(PSym.Semi).lw.?) map {
    case (a, s) => k => ap: PAnnotationsPosition => PFields(ap.annotations, k, a, s)(ap.pos)
  })

  def functionDecl[$: P]: P[PKw.Function => PAnnotationsPosition => PFunction] = P((idndef ~ argList(formalArg) ~ PSym.Colon ~ typ
    ~~ semiSeparated(precondition) ~~ semiSeparated(postcondition) ~~~ bracedExp.lw.?
  ) map { case (idn, args, c, typ, d, e, f) => k =>
      ap: PAnnotationsPosition => PFunction(ap.annotations, k, idn, args, c, typ, d, e, f)(ap.pos)
  })


  def precondition(implicit ctx : P[_]) : P[PSpecification[PKw.PreSpec]] = P((P(PKw.Requires) ~ exp).map((PSpecification.apply _).tupled).pos | ParserExtension.preSpecification(ctx))

  def postcondition(implicit ctx : P[_]) : P[PSpecification[PKw.PostSpec]] = P((P(PKw.Ensures) ~ exp).map((PSpecification.apply _).tupled).pos | ParserExtension.postSpecification(ctx))

  def predicateDecl[$: P]: P[PKw.Predicate => PAnnotationsPosition => PPredicate] = P(idndef ~ argList(formalArg) ~~~ bracedExp.lw.?).map {
    case (idn, args, c) => k =>
      ap: PAnnotationsPosition => PPredicate(ap.annotations, k, idn, args, c)(ap.pos)
  }

  def methodDecl[$: P]: P[PKw.Method => PAnnotationsPosition => PMethod] =
    P((idndef ~ argList(formalArg) ~~~ methodReturns.lw.? ~~ semiSeparated(precondition) ~~ semiSeparated(postcondition) ~~~ stmtBlock().lw.?) map {
        case (idn, args, rets, pres, posts, body) => k =>
          ap: PAnnotationsPosition => PMethod(ap.annotations, k, idn, args, rets, pres, posts, body)(ap.pos)
    })

  def methodReturns[$: P]: P[PMethodReturns] = P((P(PKw.Returns) ~ argList(idnTypeBinding.map(PFormalReturnDecl(_)))) map (PMethodReturns.apply _).tupled).pos

  def entireProgram[$: P]: P[PProgram] = P(Start ~ programDecl ~ End)

  def end[$: P]: P[Unit] = Pass ~ End

  def parseFile(file: Path, s: String): PProgram = {
    ////
    // Setup
    ////

    _file = file
    // Add an empty line at the end to make `computeFrom(s.length)` return
    // `(lines.length, 1)`, as the old implementation of `computeFrom` used to do.
    val lines = s.linesWithSeparators
    _line_offset = (lines.map(_.length) ++ Seq(0)).toArray
    var offset = 0
    for (i <- _line_offset.indices) {
      val line_length = _line_offset(i)
      _line_offset(i) = offset
      offset += line_length
    }

    ////
    // Parsing
    ////

    // Assume entire file is correct and try parsing it quickly
    fastparse.parse(s, entireProgram(_)) match {
      case Parsed.Success(value, _) => return value
      case _: Parsed.Failure =>
    }
    // There was a parsing error, parse member by member to get all errors
    var startIndex = 0
    var members: Seq[PMember] = Nil
    var errors: Seq[ParseError] = Nil
    var logFailure = true

    var res = fastparse.parse(s, end(_))
    while (!res.isSuccess) {
      startIndex = res.asInstanceOf[fastparse.Parsed.Failure].index
      fastparse.parse(s, programMember(_), false, startIndex) match {
        case fastparse.Parsed.Success(newMember, newIndex) =>
          members = members :+ newMember
          assert(startIndex < newIndex)
          startIndex = newIndex
          logFailure = true
        case fail: fastparse.Parsed.Failure =>
          // Advance index
          if (startIndex < fail.index) {
            // We partially parsed a member, but then failed to parse the rest.
            // We should log the failure regardless of the previous iteration.
            startIndex = fail.index
            logFailure = true
          } else {
            // We failed to parse anything, so simply advance by one character.
            // We may want to do this advancing using e.g. negative lookahead
            // for `programMember` with fastparse if this is too slow. Failure
            // will be logged only if previous iteration was a success.
            startIndex += 1
          }
          // Log failure
          if (logFailure) {
            val trace = fail.trace()
            val fullStack = fastparse.Parsed.Failure.formatStack(trace.input, trace.stack)
            val msg = s"${trace.aggregateMsg}. Occurred while parsing: $fullStack"
            val fPos = FilePosition(lineCol.getPos(trace.index))
            val pos = SourcePosition(fPos.file, fPos, fPos)
            errors = errors :+ ParseError(msg, pos)
            logFailure = false
          }
      }
      res = fastparse.parse(s, end(_), false, startIndex)
    }
    val warnings = _warnings
    _warnings = Nil
    val pos = (FilePosition(lineCol.getPos(0)), FilePosition(lineCol.getPos(res.get.index)))
    PProgram(Nil, members)(pos, errors ++ warnings)
  }

  object ParserExtension extends ParserPluginTemplate {

    import ParserPluginTemplate._

    /**
      * These private variables are the storage variables for each of the extensions.
      * As the parser are evaluated lazily, it is possible for us to stores extra parsing sequences in these variables
      * and after the plugins are loaded, the parsers are added to these variables and when any parser is required,
      * can be referenced back.
      */
    private var _newDeclAtEnd: Option[Extension[PAnnotationsPosition => PExtender with PMember]] = None
    private var _newDeclAtStart: Option[Extension[PAnnotationsPosition => PExtender with PMember]] = None

    private var _newExpAtEnd: Option[Extension[PExp]] = None
    private var _newExpAtStart: Option[Extension[PExp]] = None

    private var _newStmtAtEnd: Option[Extension[PStmt]] = None
    private var _newStmtAtStart: Option[Extension[PStmt]] = None

    private var _preSpecification: Option[Extension[PSpecification[PKw.PreSpec]]] = None
    private var _postSpecification: Option[Extension[PSpecification[PKw.PostSpec]]] = None
    private var _invSpecification: Option[Extension[PSpecification[PKw.InvSpec]]] = None

    private var _extendedKeywords: Set[PKeyword] = Set()


    /**
      * For more details regarding the functionality of each of these initial parser extensions
      * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
      */
    override def newDeclAtStart : Extension[PAnnotationsPosition => PExtender with PMember] = _newDeclAtStart match {
      case None => super.newDeclAtStart
      case Some(ext) => ext
    }

    override def newDeclAtEnd : Extension[PAnnotationsPosition => PExtender with PMember] = _newDeclAtEnd match {
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

    override def extendedKeywords : Set[PKeyword] = _extendedKeywords

    def addNewDeclAtEnd(t: Extension[PAnnotationsPosition => PExtender with PMember]) : Unit = _newDeclAtEnd match {
      case None => _newDeclAtEnd = Some(t)
      case Some(s) => _newDeclAtEnd = Some(combine(s, t))
    }

    def addNewDeclAtStart(t: Extension[PAnnotationsPosition => PExtender with PMember]) : Unit = _newDeclAtStart match {
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

    def addNewKeywords(t : Set[PKeyword]) : Unit = {
      _extendedKeywords ++= t
    }
  }
}