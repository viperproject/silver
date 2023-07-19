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
            val localPath = current.resolveSibling(ip.file.file).normalize()
            if (fromLocal) {
              if(!localsToImport.contains(localPath)){
                ip.resolved = localPath
                localsToImport.append(localPath)
                localImportStatements.update(localPath, ip)
              }
            } else {
              // local import get transformed to standard imports
              if (!standardsToImport.contains(localPath)) {
                ip.resolved = localPath
                ip.local = false
                standardsToImport.append(localPath)
                standardImportStatements.update(localPath, ip)
              }
            }
          } else {
            val standardPath = Paths.get(ip.file.file).normalize()
            if(!standardsToImport.contains(standardPath)){
              ip.resolved = standardPath
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

  // Actual Parser starts from here
  def identStarts[$: P] = CharIn("A-Z", "a-z", "$_")
  def identContinues[$: P] = CharIn("0-9", "A-Z", "a-z", "$_")

  def keywordLang[$: P](check: => P[_]): P[PKeywordLang] = P(FP(check.!).map { case (pos, k) => PKeywordLang(k)(pos) } ~~ !identContinues)./
  def keywordStmt[$: P](check: => P[_]): P[PKeywordStmt] = P(FP(check.!).map { case (pos, k) => PKeywordStmt(k)(pos) } ~~ !identContinues)./
  def keywordConst[$: P](check: => P[_]): P[PKeywordConstant] = P(FP(check.!).map { case (pos, k) => PKeywordConstant(k)(pos) } ~~ !identContinues)./
  def keywordType[$: P](check: => P[_]): P[PKeywordType] = P(FP(check.!).map { case (pos, k) => PKeywordType(k)(pos) } ~~ !identContinues)./

  def keywordOp[$: P](check: => P[_]): P[PKeywordOperator] = P(FP(check.!).map { case (pos, op) => PKeywordOperator(op)(pos) } ~~ !identContinues)./
  def operator[$: P](check: => P[_], clashes: => Option[P[_]] = None): P[POperatorSymbol] = P(!clashes.getOrElse(Fail) ~~ FP(check.!).map { case (pos, op) => POperatorSymbol(op)(pos) })./
  
  def parens[$: P, T](p: => P[T]) = "(" ~ p ~ ")"

  def angles[$: P, T](p: => P[T]) = "<" ~ p ~ ">"

  def quoted[$: P, T](p: => P[T]) = "\"" ~ p ~ "\""

  def block[$: P, T <: PNode](p: => P[T]): P[PBlock[T]] = FP("{" ~/ p ~ "}"./).map { case (pos, inner) => PBlock(inner)(pos) }

  def foldPExp[E <: PExp](e: E, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) => a(t) }

  def isFieldAccess(obj: Any) = {
    obj.isInstanceOf[PFieldAccess]
  }

  def atom(bracketed: Boolean = false)(implicit ctx : P[_]) : P[PExp] = P(ParserExtension.newExpAtStart(ctx) | annotatedAtom
    | integer | booltrue | boolfalse | nul | old
    | result | unExp
    | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
    | builtinTypeConstr | size | seqRange
    | mapDomain | mapRange
    | newExp | maybeTypedFuncApp(bracketed) | idnuse | ParserExtension.newExpAtEnd(ctx))

  def atomParen[$: P](bracketed: Boolean = false): P[PExp] = P(parens(expParen(true)).map(e => { e.bracketed = true; e }) | atom(bracketed))

  def stringLiteral[$: P]: P[String] = P("\"" ~ CharsWhile(_ != '\"').! ~ "\"")

  def annotation[$: P]: P[PAnnotation] = FP(operator("@") ~~ annotationIdentifier ~ parens(stringLiteral.rep(sep = ","./))).map {
    case (pos, (op, ident, args)) => PAnnotation(op, ident, args)(pos)
  }

  def annotated[$: P, T](inner: => P[PAnnotationsPosition => T]): P[T] = FP(annotation.rep(0) ~ inner).map {
    case (pos, (annotations, i)) => i(PAnnotationsPosition(annotations, pos))
  }

  def annotatedAtom[$: P]: P[PExp] = FP(annotation ~ atomParen()).map {
    case (pos, (ann, exp)) => PAnnotatedExp(ann, exp)(pos)
  }

  def result[$: P]: P[PResultLit] = keywordLang("result").map(k => PResultLit(k)(k.pos))

  def unExp[$: P]: P[PUnExp] = FP((operator(CharIn("\\-\\!"))) ~ suffixExpr()).map { case (pos, (a, b)) => PUnExp(a, b)(pos) }

  def strInteger[$: P]: P[String] = P(CharIn("0-9").rep(1)).!

  def integer[$: P]: P[PIntLit] = FP(strInteger.filter(s => s.matches("\\S+"))).map { case (pos, s) => PIntLit(BigInt(s))(pos) }

  def booltrue[$: P]: P[PBoolLit] = keywordConst("true").map(k => PBoolLit(k, true)(k.pos))

  def boolfalse[$: P]: P[PBoolLit] = keywordConst("false").map(k => PBoolLit(k, false)(k.pos))

  def nul[$: P]: P[PNullLit] = keywordConst("null").map(k => PNullLit(k)(k.pos))

  def identifier[$: P]: P[Unit] = identStarts ~~ identContinues.repX

  def annotationIdentifier[$: P]: P[String] = (identStarts ~~ CharIn("0-9", "A-Z", "a-z", "$_.").repX).!

  def ident[$: P]: P[String] = identifier.!.filter(a => !keywords.contains(a)).opaque("identifier")

  def idnuse[$: P]: P[PIdnUse] = FP(ident).map { case (pos, id) => PIdnUse(id)(pos) }

  def oldLabel[$: P]: P[PIdnUse] = idnuse | FP(LabelledOld.LhsOldLabel.!).map {
    case (pos, lhsOldLabel) => PIdnUse(lhsOldLabel)(pos)
  }

  def old[$: P]: P[PExp] = FP(keywordOp("old") ~ ("[" ~ oldLabel ~ "]").? ~ parens(exp)).map {
    case (pos, (k, a, b)) => POldExp(k, a, b)(pos)
  }

  def magicWandExp[$: P](bracketed: Boolean = false): P[PExp] = FP(orExp(bracketed) ~~~ (operator("--*") ~ exp).lw.?).map {
    case (pos, (lhs, b)) => b match {
      case Some((op, rhs)) => PMagicWandExp(lhs, op, rhs)(pos)
      case None =>lhs
  }}

  def realMagicWandExp[$: P]: P[PMagicWandExp] = FP(orExp() ~ operator("--*") ~ exp).map {
    case (pos, (lhs, op, rhs)) => PMagicWandExp(lhs, op, rhs)(pos)
  }

  def implExp[$: P](bracketed: Boolean = false): P[PExp] = FP(magicWandExp(bracketed) ~~~ (operator("==>") ~ implExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def iffExp[$: P](bracketed: Boolean = false): P[PExp] = FP(implExp(bracketed) ~~~ (operator("<==>") ~ iffExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some((op, c)) => PBinExp(a, op, c)(pos)
      case None => a
    }
  }

  def iteExpr[$: P](bracketed: Boolean = false): P[PExp] = FP(iffExp(bracketed) ~~~ (operator("?") ~ iteExpr() ~ operator(":") ~ iteExpr()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some((q, thn, c, els)) => PCondExp(a, q, thn, c, els)(pos)
      case None => a
    }
  }

  def expParen[$: P](bracketed: Boolean): P[PExp] = P(iteExpr(bracketed))

  def exp[$: P]: P[PExp] = P(expParen(false))

  def indexSuffix[$: P]: P[((Position, Position), PExp) => SuffixedExpressionGenerator[PExp]] = P(
    (":=" ~/ exp).map(v => (pos: (Position, Position), i: PExp) => SuffixedExpressionGenerator[PExp](e => PUpdate(e, i, v)(e.pos._1, pos._2))) |
    // Need to have `".." ~ exp` before `".." ~ Pass` and both of those before `Pass` to avoid issues due to some implicit cut when `indexSuffix` succeeds
    (".." ~ exp).map(m => (pos: (Position, Position), n: PExp) => SuffixedExpressionGenerator[PExp](e => PSeqDrop(PSeqTake(e, m)(e.pos._1, pos._2), n)(e.pos._1, pos._2))) |
    (".." ~ Pass).map(_ => (pos: (Position, Position), n: PExp) => SuffixedExpressionGenerator[PExp](e => PSeqDrop(e, n)(e.pos._1, pos._2))) |
    Pass.map(_ => (pos: (Position, Position), e1: PExp) => SuffixedExpressionGenerator[PExp](e0 => PLookup(e0, e1)(e0.pos._1, pos._2))))

  def suffix[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(FP((!".." ~~ ".") ~/ idnuse).map { case (pos, id) => SuffixedExpressionGenerator[PExp](e => PFieldAccess(e, id)(e.pos._1, pos._2)) } |
      FP("[" ~ ".." ~/ exp ~ "]").map { case (pos, n) => SuffixedExpressionGenerator[PExp](e => PSeqTake(e, n)(e.pos._1, pos._2)) } |
      FP("[" ~ exp ~ indexSuffix ~ "]").map { case (pos, (e, s)) => s(pos, e) })

  def suffixExpr[$: P](bracketed: Boolean = false): P[PExp] = P((atomParen(bracketed) ~~~ suffix.lw.rep).map { case (fac, ss) => foldPExp(fac, ss) })

  def termOp[$: P]: P[POperatorSymbol] = operator(StringIn("*", "/", "\\", "%"))

  def term[$: P](bracketed: Boolean = false): P[PExp] = P((suffixExpr(bracketed) ~~~ termd.lw.rep).map { case (a, ss) => foldPExp(a, ss) })

  def termd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = FP(termOp ~/ suffixExpr()).map { case (pos, (op, id)) => SuffixedExpressionGenerator(e => PBinExp(e, op, id)(e.pos._1, pos._2)) }

  def sumOp[$: P]: P[POperator] = P(operator(StringIn("++", "+", "-"), Some("--*")) | keywordOp(StringIn("union", "intersection", "setminus", "subset")))

  def sum[$: P](bracketed: Boolean = false): P[PExp] = P((term(bracketed) ~~~ sumd.lw.rep).map { case (a, ss) => foldPExp(a, ss) })

  def sumd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = FP(sumOp ~/ term()).map { case (pos, (op, id)) => SuffixedExpressionGenerator(e => PBinExp(e, op, id)(e.pos._1, pos._2)) }

  def cmpOp[$: P]: P[POperator] = P(operator(StringIn("<=", ">=", "<", ">"), Some("<==>")) | keywordOp("in"))

  val cmpOps = Set("<=", ">=", "<", ">", "in")

  def cmpd[$: P]: P[PExp => SuffixedExpressionGenerator[PBinExp]] = FP(cmpOp ~/ sum()).map {
    case (pos, (op, right)) => chainComp(op, right, pos)
  }

  def chainComp(op: POperator, right: PExp, pos: (FilePosition, FilePosition))(from: PExp) = SuffixedExpressionGenerator(_ match {
      case left@PBinExp(_, op0, middle) if cmpOps.contains(op0.operator) && left != from =>
        PBinExp(left, POperatorSymbol("&&")(NoPosition, NoPosition), PBinExp(middle, op, right)(middle.pos._1, pos._2))(left.pos._1, pos._2)
      case left@PBinExp(_, POperatorSymbol("&&"), PBinExp(_, op0, middle)) if cmpOps.contains(op0.operator) && left != from =>
        PBinExp(left, POperatorSymbol("&&")(NoPosition, NoPosition), PBinExp(middle, op, right)(middle.pos._1, pos._2))(left.pos._1, pos._2)
      case left => PBinExp(left, op, right)(left.pos._1, pos._2)
  })

  def cmpExp[$: P](bracketed: Boolean = false): P[PExp] = P((sum(bracketed) ~~~ cmpd.lw.rep).map {
    case (from, others) => foldPExp(from, others.map(_(from)))
  })

  def eqOp[$: P] = P(operator(StringIn("==", "!="), Some("==>")))

  def eqExpParen[$: P](bracketed: Boolean = false): P[PExp] = FP(cmpExp(bracketed) ~~~ (eqOp ~/ eqExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }
  def eqExp[$: P]: P[PExp] = eqExpParen()

  def andExp[$: P](bracketed: Boolean = false): P[PExp] = FP(eqExpParen(bracketed) ~~~ (operator("&&") ~ andExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def orExp[$: P](bracketed: Boolean = false): P[PExp] = FP(andExp(bracketed) ~~~ (operator("||") ~ orExp()).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def accessPredImpl[$: P]: P[PAccPred] = FP(keywordOp("acc") ~ "(" ~ locAcc ~ ("," ~/ exp).? ~ ")").map {
    case (pos, (k, loc, perms)) => {
      PAccPred(k, loc, perms.getOrElse(PFullPerm.implied()))(pos)
    }
  }

  def accessPred[$: P]: P[PAccPred] = accessPredImpl

  def resAcc[$: P]: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  def locAcc[$: P]: P[PLocationAccess] = P(fieldAcc | predAcc)

  def fieldAcc[$: P]: P[PFieldAccess] =
    P(NoCut(suffixExpr().filter(isFieldAccess)).map {
      case fa: PFieldAccess => fa
      case other => sys.error(s"Unexpectedly found $other")
    })

  def predAcc[$: P]: P[PLocationAccess] = funcApp

  def actualArgList[$: P]: P[Seq[PExp]] = exp.rep(sep = ","./)

  def inhaleExhale[$: P]: P[PExp] = FP("[" ~ NoCut(exp) ~ "," ~/ exp ~ "]").map {
    case (pos, (a, b)) => PInhaleExhaleExp(a, b)(pos)
  }

  def perm[$: P]: P[PExp] =
    P(keywordConst("none").map(k => PNoPerm(k)(k.pos)) |
      keywordConst("wildcard").map(k => PWildcard(k)(k.pos)) |
      keywordConst("write").map(k => PFullPerm(k)(k.pos)) |
      keywordConst("epsilon").map(k => PEpsilon(k)(k.pos)) |
      FP(keywordOp("perm") ~ parens(resAcc)).map{ case (pos, (k, r)) => PCurPerm(k, r)(pos)})

  def let[$: P]: P[PExp] =
    FP(keywordOp("let") ~/ idndef ~ "==" ~/ "(" ~ exp ~ ")" ~ keywordOp("in") ~/ exp).map {
      case (pos, (k, id, exp1, in, exp2)) =>
      /* Type unresolvedType is expected to be replaced with the type of exp1
       * after the latter has been resolved
       * */
      val unresolvedType = PUnknown()(id.pos)
      val logicalVar = PLogicalVarDecl(id, unresolvedType)(id.pos)
      val nestedScope = PLetNestedScope(logicalVar, exp2)(exp2.pos)

      PLet(k, exp1, in, nestedScope)(pos)
    }

  def idndef[$: P]: P[PIdnDef] = FP(ident).map {
    case (pos, s) =>
      PIdnDef(s)(pos)
    }

  def quant[$: P]: P[PExp] = P(FP(keywordLang("forall") ~ nonEmptyIdnTypeList ~ operator("::") ~ trigger.rep ~ exp).map {
    case (pos, (k, a, o, b, c)) =>
      PForall(k, a.map(PLogicalVarDecl(_)), o, b, c)(pos)
    } |
    FP(keywordLang("exists") ~ nonEmptyIdnTypeList ~ operator("::") ~ trigger.rep ~ exp).map {
      case (pos, (k, a, o, b, c)) =>
        PExists(k, a.map(PLogicalVarDecl(_)), o, b, c)(pos)
    })

  def nonEmptyIdnTypeList[$: P]: P[Seq[PIdnTypeBinding]] = P(idnTypeBinding.rep(min = 1, sep = ","./))

  def idnTypeBinding[$: P]: P[PIdnTypeBinding] = FP(idndef ~ ":" ~/ typ).map { case (pos, (a, b)) => PIdnTypeBinding(a, b)(pos) }

  def typ[$: P]: P[PType] = P(primitiveTyp | domainTyp | seqType | setType | multisetType | mapType | macroType)

  def domainTyp[$: P]: P[PDomainType] = P(FP(idnuse ~ "[" ~ typ.rep(sep = ","./) ~ "]").map { case (pos, (a, b)) => PDomainType(a, b)(pos) } |
    // domain type without type arguments (might also be a type variable)
    idnuse.map(name => {
      PDomainType(name, Nil)(name.pos)
    }))

  def seqType[$: P]: P[PSeqType] = FP(keywordType("Seq") ~ "[" ~ typ ~ "]").map{ case (pos, (k, t)) => PSeqType(k, t)(pos)}

  def setType[$: P]: P[PSetType] = FP(keywordType("Set") ~ "[" ~ typ ~ "]").map{ case (pos, (k, t)) => PSetType(k, t)(pos)}

  def multisetType[$: P]: P[PMultisetType] = FP(keywordType("Multiset") ~ "[" ~ typ ~ "]").map{ case (pos, (k, t)) => PMultisetType(k, t)(pos)}

  // Maps:
  def mapType[$: P] : P[PMapType] = FP(keywordType("Map") ~ "[" ~ typ ~ "," ~ typ ~ "]").map {
   case (pos, (k, keyType, valueType)) => PMapType(k, keyType, valueType)(pos)
  }

  def primitiveTyp[$: P]: P[PPrimitiv] = P(keywordType("Rational").map {
    case name =>
      val pos = name.pos.asInstanceOf[(HasLineColumn, HasLineColumn)]
      _warnings = _warnings :+ ParseWarning("Rational is deprecated, use Perm instead", SourcePosition(_file, pos._1, pos._2))
      PPrimitiv(PKeywordType("Perm")(name.pos))(name.pos)
  } | keywordType(StringIn("Int", "Bool", "Perm", "Ref")).map { case name => PPrimitiv(name)(name.pos) })

  /** Only for call-like macros, `idnuse`-like ones are parsed by `domainTyp`. */
  def macroType[$: P] : P[PMacroType] = funcApp.map(PMacroType(_))

  def trigger[$: P]: P[PTrigger] = FP("{" ~/ exp.rep(sep = ","./) ~ "}"./).map{
    case (pos, s) => PTrigger(s)(pos)
  }

  def forperm[$: P]: P[PExp] = FP(keywordLang("forperm") ~ nonEmptyIdnTypeList ~ "[" ~ resAcc ~ "]" ~ operator("::") ~ exp).map {
    case (pos, (k, args, res, op, body)) => PForPerm(k, args.map(PLogicalVarDecl(_)), res, op, body)(pos)
  }

  def unfolding[$: P]: P[PExp] = FP(keywordOp("unfolding") ~ predicateAccessPred ~ keywordOp("in") ~ exp).map {
    case (pos, (op, a, in, b)) => PUnfolding(op, a, in, b)(pos) }

  def predicateAccessPred[$: P]: P[PAccPred] = P(accessPred | FP(predAcc).map {
    case (pos, loc) => PAccPred(PKeywordOperator("acc")(NoPosition, NoPosition), loc, PFullPerm.implied())(pos)
  })

  def builtinTypeConstr[$: P]: P[PExp] = setConstructor | seqConstructor | multiSetConstructor | mapConstructor

  def setConstructor[$: P]: P[PExp] = builtinConstructor("Set", typ, exp)(t => PEmptySet(_, t.getOrElse(PTypeVar("#E")))(_), v => PExplicitSet(_, v)(_))

  def seqConstructor[$: P]: P[PExp] = builtinConstructor("Seq", typ, exp)(t => PEmptySeq(_, t.getOrElse(PTypeVar("#E")))(_), v => PExplicitSeq(_, v)(_))

  def multiSetConstructor[$: P]: P[PExp] = builtinConstructor("Multiset", typ, exp)(t => PEmptyMultiset(_, t.getOrElse(PTypeVar("#E")))(_), v => PExplicitMultiset(_, v)(_))

  def mapConstructor[$: P]: P[PExp] = builtinConstructor("Map", typ ~ "," ~ typ, maplet)(t => PEmptyMap(_, t.map(_._1).getOrElse(PTypeVar("#K")), t.map(_._2).getOrElse(PTypeVar("#E")))(_), v => PExplicitMap(_, v)(_))

  def builtinConstructor[$: P, T, E](name: => P[_], types: => P[T], element: => P[E])(empty: Option[T] => (PKeywordOperator, (Position, Position)) => PExp, nonEmpty: Seq[E] => (PKeywordOperator, (Position, Position)) => PExp): P[PExp] =
    FP(keywordOp(name) ~ ((("[" ~ types ~ "]").? ~ "(" ~ ")").map(empty) | ("(" ~ element.rep(sep = ","./, min = 1) ~ ")").map(nonEmpty))).map { case (pos, (k, exp)) => exp(k, pos) }

  def size[$: P]: P[PExp] = P(FP("|" ~/ exp ~ "|"./).map {
    case (pos, e) => PSize(e)(pos)
  })

  def seqRange[$: P]: P[PExp] = FP("[" ~ NoCut(exp) ~ ".." ~ exp ~ ")").map { case (pos, (a, b)) => PRangeSeq(a, b)(pos) }

  def maplet[$: P]: P[PMaplet] = P(FP(exp ~ ":=" ~/ exp).map {
    case (pos, (key, value)) => PMaplet(key, value)(pos)
  })

  def mapDomain[$: P]: P[PExp] = P(FP(keywordOp("domain") ~ "(" ~ exp ~ ")").map {
    case (pos, (k, e)) => PMapDomain(k, e)(pos)
  })

  def mapRange[$: P] : P[PExp] = P(FP(keywordOp("range") ~ "(" ~ exp ~ ")").map {
    case (pos, (k, e)) => PMapRange(k, e)(pos)
  })

  def newExp[$: P]: P[PNewExp] = FP(keywordOp("new") ~ "(" ~ newExpFields ~ ")").map { case (pos, (k, fields)) => PNewExp(k, fields)(pos) }

  def newExpFields[$: P]: P[Option[Seq[PIdnUse]]] = P(P("*").map(_ => None) | P(idnuse.rep(sep = ","./)).map(Some(_)))

  def funcApp[$: P]: P[PCall] = FP(idnuse ~ parens(actualArgList)).map {
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

  def assign[$: P]: P[PAssign] = FP(assignTarget.rep(min = 1, sep = ","./) ~ operator(":=") ~ exp).map { case (pos, (targets, op, rhs)) => PAssign(targets, Some(op), rhs)(pos) }

  def methodCall[$: P]: P[PAssign] = FP(funcApp | idnuse).map { case (pos, rhs) => PAssign(Nil, None, rhs)(pos) }

  def fold[$: P]: P[PFold] = FP(keywordStmt("fold") ~ predicateAccessPred).map{ case (pos, (k, e)) => PFold(k, e)(pos)}

  def unfold[$: P]: P[PUnfold] = FP(keywordStmt("unfold") ~ predicateAccessPred).map{ case (pos, (k, e)) => PUnfold(k, e)(pos)}

  def exhale[$: P]: P[PExhale] = FP(keywordStmt("exhale") ~ exp).map{ case (pos, (k, e)) => PExhale(k, e)(pos) }

  def assertStmt[$: P]: P[PAssert] = FP(keywordStmt("assert") ~ exp).map{ case (pos, (k, e)) => PAssert(k, e)(pos) }

  def inhale[$: P]: P[PInhale] = FP(keywordStmt("inhale") ~ exp).map{ case (pos, (k, e)) => PInhale(k, e)(pos) }

  def assume[$: P]: P[PAssume] = FP(keywordStmt("assume") ~ exp).map{ case (pos, (k, e)) => PAssume(k, e)(pos) }

  // Parsing Havoc statements
  // Havoc statements have two forms:
  // in the grammar. Note that it is still possible to express "(<exp1> ==> <exp2>) ==> <resource>
  // using parentheses.

  // Havocall follows a similar pattern to havoc but allows quantifying over variables.

  def quasihavoc[$: P]: P[PQuasihavoc] = FP(keywordStmt("quasihavoc") ~
    (NoCut(magicWandExp()) ~ operator("==>")).? ~ exp ).map {
      case (pos, (k, lhs, rhs)) => PQuasihavoc(k, lhs, rhs)(pos)
  }

  def quasihavocall[$: P]: P[PQuasihavocall] = FP(keywordStmt("quasihavocall") ~
    nonEmptyIdnTypeList ~ operator("::") ~ (NoCut(magicWandExp()) ~ operator("==>")).? ~ exp).map {
    case (pos, (k, vars, c, lhs, rhs)) => PQuasihavocall(k, vars.map(PLogicalVarDecl(_)), c, lhs, rhs)(pos)
  }

  def ifThenElse[$: P]: P[PIf] = FP(keywordStmt("if") ~ "(" ~ exp ~ ")" ~ stmtBlock ~~~ elseIfOrElse).map {
    case (pos, (k, cond, thn, (eleKw, ele))) => PIf(k, cond, thn, eleKw, ele)(pos)
  }

  def stmtBlock[$: P]: P[PSeqn] =  FP("{" ~ (stmt ~/ ";".?).rep ~ "}").map{ case (pos, e) => PSeqn(e)(pos)}

  def elseIfOrElse[$: P]: LW[(Option[PKeywordStmt], PSeqn)] = elseIf.lw | elseBlock

  def elseIf[$: P]: P[(Option[PKeywordStmt], PSeqn)] = FP(keywordStmt("elseif") ~ "(" ~ exp ~ ")" ~ stmtBlock ~~~ elseIfOrElse).map {
    case (pos, (k, cond, thn, (eleKw, ele))) => (Some(k), PSeqn(Seq(PIf(k, cond, thn, eleKw, ele)(pos)))(pos))
  }

  def elseBlock[$: P]: LW[(Option[PKeywordStmt], PSeqn)] = (
    (keywordStmt("else") ~/ stmtBlock).map(p => (Some(p._1), p._2)) |
    FP(Pass).map { case (pos, _) => (None, PSeqn(Nil)(pos)) }
  ).lw

  def whileStmt[$: P]: P[PWhile] = FP(keywordStmt("while") ~ "(" ~ exp ~ ")" ~ invariant.rep ~ stmtBlock).map {
    case (pos, (k, cond, invs, body)) =>
      PWhile(k, cond, invs, body)(pos)
  }

  def invariant(implicit ctx : P[_]) : P[(PKeywordLang, PExp)] = P((keywordLang("invariant") ~ exp ~~~ ";".lw.?) | ParserExtension.invSpecification(ctx))

  def localVars[$: P]: P[PVars] = FP(keywordStmt("var") ~ nonEmptyIdnTypeList ~~~ (operator(":=") ~ exp).lw.?).map {
    case (pos, (k, a, b)) => PVars(k, a.map(PLocalVarDecl(_)), b)(pos)
  }

  def defineDecl[$: P]: P[PAnnotationsPosition => PDefine] = P(keywordLang("define") ~ idndef ~ ("(" ~ idndef.rep(sep = ","./) ~ ")").? ~ (
    FP("{" ~/ (nodefinestmt ~ ";".?).rep ~ "}"./).map { case (pos, c) => (k: PKeywordLang, a: PIdnDef, b: Option[Seq[PIdnDef]]) => ap: PAnnotationsPosition => PDefine(ap.annotations, k, a, b, PSeqn(c)(pos))(ap.pos) } |
    exp.map(e => (k: PKeywordLang, a: PIdnDef, b: Option[Seq[PIdnDef]]) => (ap: PAnnotationsPosition) => PDefine(ap.annotations, k, a, b, e)(ap.pos)))).map {
      case (k, a, b, c) => c(k, a, b)
  }
  def defineDeclStmt[$: P]: P[PDefine] = FP(defineDecl).map { case (pos, e) => e(PAnnotationsPosition(Nil, pos)) }

  def goto[$: P]: P[PGoto] = FP(keywordStmt("goto") ~ idnuse).map{ case (pos, (k, e)) => PGoto(k, e)(pos) }

  def label[$: P]: P[PLabel] = FP(keywordStmt("label") ~/ idndef ~~~ (keywordLang("invariant") ~/ exp).lw.rep).map {
    case (pos, (k, name, invs)) => PLabel(k, name, invs)(pos) }

  def packageWand[$: P]: P[PPackageWand] = FP(keywordStmt("package") ~ magicWandExp() ~~~ stmtBlock.lw.?).map {
    case (pos, (k, wand, Some(proofScript))) =>
      PPackageWand(k, wand, proofScript)(pos)
    case (pos, (k, wand, None)) =>
      PPackageWand(k, wand, PSeqn(Seq())(pos))(pos)
  }

  def applyWand[$: P]: P[PApplyWand] = FP(keywordStmt("apply") ~ magicWandExp()).map {
    case (pos, (k, p)) => PApplyWand(k, p)(pos)
  }

  def applying[$: P]: P[PExp] = FP(keywordOp("applying") ~ "(" ~ magicWandExp() ~ ")" ~ keywordOp("in") ~ exp).map { case (pos, (k, a, op, b)) => PApplying(k, a, op, b)(pos) }

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

  def preambleImport[$: P]: P[PAnnotationsPosition => PImport] = P(keywordLang("import") ~
    (quoted(relativeFilePath).map((true, _)) | angles(relativeFilePath).map((false, _)))
  ).map {
    case (k, (local, filename)) => ap: PAnnotationsPosition => PImport(ap.annotations, k, local, filename)(ap.pos)
  }

  def relativeFilePath[$: P]: P[PFilePath] = FP((CharIn("~.").? ~~ (CharIn("/").? ~~ CharIn(".", "A-Z", "a-z", "0-9", "_\\- \n\t")).rep(1)).!).map {
    case (pos, path) => PFilePath(path)(pos)
  }

  def anyString[$: P]: P[String] = P(CharPred(c => c !='\"').rep(1).!)

  def domainDecl[$: P]: P[PAnnotationsPosition => PDomain] = P(keywordLang("domain") ~ idndef ~ typeParams ~ (keywordLang("interpretation") ~ parens((ident ~ ":" ~ quoted(anyString.!)).rep(sep = ","))).? ~
    block(FP(annotated(domainFunctionDecl | axiomDecl).rep).map(ms => PDomainMembers1(ms._2)(ms._1)))).map {
    case (k, name, typparams, interpretations, block) =>
      val members = block.inner.members
      val funcs1 = members collect { case m: PDomainFunction1 => m }
      val axioms1 = members collect { case m: PAxiom1 => m }
      val funcs = funcs1 map (f => PDomainFunction(f.annotations, f.unique, f.function, f.idndef, f.formalArgs, f.typ, f.interpretation)(PIdnUse(name.name)(name.pos))(f.pos))
      val axioms = axioms1 map (a => PAxiom(a.annotations, a.axiom, a.idndef, a.exp)(PIdnUse(name.name)(name.pos))(a.pos))
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

  def domainFunctionDecl[$: P]: P[PAnnotationsPosition => PDomainFunction1] = P(keywordLang("unique").? ~ domainFunctionSignature ~ (keywordLang("interpretation") ~ quoted(anyString.!)).? ~~~ ";".lw.?).map {
    case (unique, fdecl, interpretation) => fdecl match {
      case (function, name, formalArgs, t) => ap: PAnnotationsPosition => PDomainFunction1(ap.annotations, unique, function, name, formalArgs, t, interpretation)(ap.pos)
    }
  }

  def domainFunctionSignature[$: P] = P(keywordLang("function") ~ idndef ~ "(" ~ anyFormalArgList ~ ")" ~ ":" ~ typ)

  def anyFormalArgList[$: P]: P[Seq[PAnyFormalArgDecl]] = P((formalArg | unnamedFormalArg).rep(sep = ","./))

  def formalArg[$: P]: P[PFormalArgDecl] = P(idnTypeBinding.map(PFormalArgDecl(_)))

  def unnamedFormalArg[$: P] = FP(typ).map{ case (pos, t) => PUnnamedFormalArgDecl(t)(pos) }

  def formalArgList[$: P]: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","./))

  def formalReturnList[$: P]: P[Seq[PFormalReturnDecl]] = P(idnTypeBinding.map(PFormalReturnDecl(_)).rep(sep = ","./))

  def axiomDecl[$: P]: P[PAnnotationsPosition => PAxiom1] = P(keywordLang("axiom") ~ idndef.? ~ block(exp) ~~~ ";".lw.?).map { case (k, a, b) =>
    ap: PAnnotationsPosition => PAxiom1(ap.annotations, k, a, b)(ap.pos)
  }

  def fieldDecl[$: P]: P[PAnnotationsPosition => PFields] = P(keywordLang("field") ~ nonEmptyIdnTypeList ~~~ ";".lw.?).map {
    case (k, a) => ap: PAnnotationsPosition => PFields(ap.annotations, k, a.map(PFieldDecl(_)))(ap.pos)
  }

  def functionDecl[$: P]: P[PAnnotationsPosition => PFunction] = P(keywordLang("function") ~ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~~~ precondition.lw.rep ~~~
    postcondition.lw.rep ~~~ block(exp).lw.?).map({ case (k, a, b, c, d, e, f) =>
      ap: PAnnotationsPosition => PFunction(ap.annotations, k, a, b, c, d, e, f)(ap.pos)
  })


  def precondition(implicit ctx : P[_]) : P[(PKeywordLang, PExp)] = P((keywordLang("requires") ~ exp ~~~ ";".lw.?) | ParserExtension.preSpecification(ctx))

  def postcondition(implicit ctx : P[_]) : P[(PKeywordLang, PExp)] = P((keywordLang("ensures") ~ exp ~~~ ";".lw.?) | ParserExtension.postSpecification(ctx))

  def predicateDecl[$: P]: P[PAnnotationsPosition => PPredicate] = P(keywordLang("predicate") ~ idndef ~ "(" ~ formalArgList ~ ")" ~~~ (block(exp)).lw.?).map {
    case (k, a, b, c) =>
      ap: PAnnotationsPosition => PPredicate(ap.annotations, k, a, b, c)(ap.pos)
  }

  def methodDecl[$: P]: P[PAnnotationsPosition => PMethod] = P(methodSignature ~~~/ precondition.lw.rep ~~~ postcondition.lw.rep ~~~ stmtBlock.lw.?).map {
    case (k, name, args, rets, pres, posts, body) =>
      ap: PAnnotationsPosition => PMethod(ap.annotations, k, name, args, rets.map(_._1), rets.map(_._2).getOrElse(Nil), pres, posts, body)(ap.pos)
  }

  def methodSignature[$: P] = P(keywordLang("method") ~ idndef ~ "(" ~ formalArgList ~ ")" ~~~ (keywordLang("returns") ~ "(" ~ formalReturnList ~ ")").lw.?)

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

    private var _preSpecification: Option[Extension[(PKeywordLang, PExp)]] = None
    private var _postSpecification: Option[Extension[(PKeywordLang, PExp)]] = None
    private var _invSpecification: Option[Extension[(PKeywordLang, PExp)]] = None

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

    override def postSpecification : Extension[(PKeywordLang, PExp)] = _postSpecification match {
      case None => super.postSpecification
      case Some(ext) => ext
    }

    override def preSpecification : Extension[(PKeywordLang, PExp)] = _preSpecification match {
      case None => super.preSpecification
      case Some(ext) => ext
    }

    override def invSpecification : Extension[(PKeywordLang, PExp)] = _invSpecification match {
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

    def addNewPreCondition(t: Extension[(PKeywordLang, PExp)]) : Unit = _preSpecification match {
      case None => _preSpecification = Some(t)
      case Some(s) => _preSpecification = Some(combine(s, t))
    }

    def addNewPostCondition(t: Extension[(PKeywordLang, PExp)]) : Unit = _postSpecification match {
      case None => _postSpecification = Some(t)
      case Some(s) => _postSpecification = Some(combine(s, t))
    }

    def addNewInvariantCondition(t: Extension[(PKeywordLang, PExp)]) : Unit = _invSpecification match {
      case None => _invSpecification = Some(t)
      case Some(s) => _invSpecification = Some(combine(s, t))
    }

    def addNewKeywords(t : Set[String]) : Unit = {
      _extendedKeywords ++= t
    }
  }
}