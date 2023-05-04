// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.net.URL
import java.nio.file.{Files, Path, Paths}

import viper.silver.ast.{FilePosition, LabelledOld, LineCol, NoPosition, Position, SourcePosition}
import viper.silver.ast.utility.rewriter.{ContextA, PartialContextC, StrategyBuilder}
import viper.silver.parser.FastParserCompanion.{LW, LeadingWhitespace}
import viper.silver.parser.Transformer.ParseTreeDuplicationError
import viper.silver.plugin.{ParserPluginTemplate, SilverPluginManager}
import viper.silver.verifier.{ParseError, ParseWarning}

import scala.collection.{immutable, mutable}


case class ParseException(msg: String, pos: Position) extends Exception

case class SuffixedExpressionGenerator[E <: PExp](func: PExp => E) extends (PExp => PExp) {
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
  var _file: Path = null

  def parse(s: String, f: Path, plugins: Option[SilverPluginManager] = None) = {
    // Strategy to handle imports
    // Idea: Import every import reference and merge imported methods, functions, imports, .. into current program
    //       iterate until no new imports are present.
    //       To import each file at most once the absolute path is normalized (removes redundancies).
    //       For standard import the path relative to the import folder (in resources) is normalized and used.
    //       (normalize a path is a purely syntactic operation. if sally were a symbolic link removing sally/.. might
    //       result in a path that no longer locates the intended file. toRealPath() might be an alternative)

    def resolveImports(p: PProgram) = {
        val localsToImport = new mutable.ArrayBuffer[Path]()
        val localImportStatements = new mutable.HashMap[Path, PLocalImport]()
        val standardsToImport = new mutable.ArrayBuffer[Path]()
        val standardImportStatements = new mutable.HashMap[Path, PStandardImport]()

        // assume p is a program from the user space (local).
        val filePath = f.toAbsolutePath.normalize()
        localsToImport.append(filePath)

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
            ip match {
              case localImport: PLocalImport if fromLocal =>
                val localPath = current.resolveSibling(localImport.file).normalize()
                if(!localsToImport.contains(localPath)){
                  localsToImport.append(localPath)
                  localImportStatements.update(localPath, localImport)
                }
              case localImport: PLocalImport if !fromLocal =>
                // local import get transformed to standard imports
                val localPath = current.resolveSibling(localImport.file).normalize()
                if (!standardsToImport.contains(localPath)) {
                  standardsToImport.append(localPath)
                  standardImportStatements.update(localPath, PStandardImport(localPath.toString)(localImport.pos))
                }
              case standardImport: PStandardImport =>
                val standardPath = Paths.get(standardImport.file).normalize()
                if(!standardsToImport.contains(standardPath)){
                  standardsToImport.append(standardPath)
                  standardImportStatements.update(standardPath, standardImport)
                }
            }
          }
        }

        def appendNewProgram(newProg: PProgram): Unit = {
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
            val newProg = importLocal(current, localImportStatements(current), plugins)

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
      PProgram(Seq(), macros, domains, fields, functions, predicates, methods, extensions, errors)(p.pos)
    }


    try {
      val rp = RecParser(f).parses(s)
      rp match {
        case Parsed.Success(program@PProgram(_, _, _, _, _, _, _, _, _), e) =>
          val importedProgram = resolveImports(program)                             // Import programs
          val expandedProgram = expandDefines(importedProgram)                      // Expand macros
          Parsed.Success(expandedProgram, e)
        case _ => rp
      }
    }
    catch {
      case ParseException(msg, pos) =>
        val location = pos match {
          case NoPosition =>
            SourcePosition(_file, 0, 0)
          case f: FilePosition =>
            SourcePosition(f.file, f.line, f.column)
        }

        ParseError(msg, location)
    }
  }

  case class RecParser(file: Path) {

    def parses(s: String) = {
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

      fastparse.parse(s, entireProgram(_))
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

  import scala.language.implicitConversions
  implicit def LeadingWhitespaceStr(p: String)(implicit ctx: P[Any]): LeadingWhitespace[Unit] = new LeadingWhitespace(() => P(p))
  implicit def LeadingWhitespace[T](p: => P[T]) = new LeadingWhitespace(() => p)


  // Actual Parser starts from here
  def identContinues[$: P] = CharIn("0-9", "A-Z", "a-z", "$_")

  def keyword[$: P](check: String) = check ~~ !identContinues

  def parens[$: P, T](p: => P[T]) = "(" ~ p ~ ")"

  def angles[$: P, T](p: => P[T]) = "<" ~ p ~ ">"

  def quoted[$: P, T](p: => P[T]) = "\"" ~ p ~ "\""

  def foldPExp[E <: PExp](e: PExp, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) => a(t)
    }.asInstanceOf[E]

  def isFieldAccess(obj: Any) = {
    obj.isInstanceOf[PFieldAccess]
  }

  /**
    * Function that parses a file and converts it into a program
    *
    * @param buffer Buffer to read file from
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importProgram(buffer: Array[String], path: Path, importStmt: PImport, plugins: Option[SilverPluginManager]): PProgram = {

    val imported_source = buffer.mkString("\n") + "\n"
    val transformed_source = if (plugins.isDefined){
      plugins.get.beforeParse(imported_source, isImported = true) match {
        case Some(transformed) => transformed
        case None => throw ParseException(s"Plugin failed: ${plugins.get.errors.map(_.toString).mkString(", ")}", importStmt.pos._1)
      }
    } else {
      imported_source
    }
    val p = RecParser(path).parses(transformed_source)
    p match {
      case fastparse.Parsed.Success(prog, _) => prog
      case fail @ fastparse.Parsed.Failure(_, index, _) =>
        val msg = fail.trace().longMsg
        val (line, col) = lineCol.getPos(index)
        throw ParseException(s"Expected $msg", FilePosition(path, line, col))
    }
  }

  /**
    * Opens (and closes) standard file to be imported, parses it and converts it into a program.
    * Standard files are located in the resources inside a "import" folder.
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importStandard(path: Path, importStmt: PStandardImport, plugins: Option[SilverPluginManager]): PProgram = {
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
            throw ParseException(s"could not import file ($e)", importStmt.pos._1)
        } finally {
          source.close()
        }
      } catch {
        case _: java.lang.NullPointerException =>
          throw ParseException(s"""file <$path> does not exist""", importStmt.pos._1)
        case e@(_: RuntimeException | _: java.io.IOException) =>
          throw ParseException(s"could not import file ($e)", importStmt.pos._1)
      }

    //scala.io.Source.fromInputStream(getClass.getResourceAsStream("/import/"+ path.toString))
    importProgram(buffer, path, importStmt, plugins)
  }

  /**
    * Opens (and closes) local file to be imported, parses it and converts it into a program.
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importLocal(path: Path, importStmt: PImport, plugins: Option[SilverPluginManager]): PProgram = {
    if (java.nio.file.Files.notExists(path)) {
      throw ParseException(s"""file "$path" does not exist""", importStmt.pos._1)
    }

    _file = path
    val source = scala.io.Source.fromInputStream(Files.newInputStream(path))

    val buffer = try {
      source.getLines().toArray
    } catch {
      case e@(_: RuntimeException | _: java.io.IOException) =>
        throw ParseException(s"""could not import file ($e)""", importStmt.pos._1)
    } finally {
      source.close()
    }

    importProgram(buffer, path, importStmt, plugins)
  }

  /**
    * Expands the macros of a PProgram
    *
    * @param p PProgram with macros to be expanded
    * @return PProgram with expanded macros
    */
  def expandDefines(p: PProgram): PProgram = {
    val globalMacros = p.macros

    // Collect names to check for and avoid clashes
    val globalNamesWithoutMacros: Set[String] = (
         p.domains.map(_.idndef.name).toSet
      ++ p.functions.map(_.idndef.name).toSet
      ++ p.predicates.map(_.idndef.name).toSet
      ++ p.methods.map(_.idndef.name).toSet
    )

    // Check if all macros names are unique
    val uniqueMacroNames = new mutable.HashMap[String, Position]()
    for (define <- globalMacros) {
      if (uniqueMacroNames.contains(define.idndef.name)) {
        throw ParseException(s"Another macro named '${define.idndef.name}' already " +
          s"exists at ${uniqueMacroNames(define.idndef.name)}", define.pos._1)
      } else {
        uniqueMacroNames += ((define.idndef.name, define.pos._1))
      }
    }

    // Check if macros names aren't already taken by other identifiers
    for (name <- globalNamesWithoutMacros) {
      if (uniqueMacroNames.contains(name)) {
        throw ParseException(s"The macro name '$name' has already been used by another identifier", uniqueMacroNames(name))
      }
    }

    // Check if macros are defined in the right place
    case class InsideMagicWandContext(inside: Boolean = false)
    StrategyBuilder.ContextVisitor[PNode, InsideMagicWandContext](
      {
        case (_: PPackageWand, c) => c.updateContext(c.c.copy(true))
        case (d: PDefine, c) if c.c.inside => throw ParseException("Macros cannot be defined inside magic wands proof scripts", d.pos._1)
        case (_, c) => c
      }, InsideMagicWandContext()).execute(p)

    // Check if all macro parameters are used in the body
    def allParametersUsedInBody(define: PDefine): Seq[ParseWarning] = {
      val parameters = define.parameters.getOrElse(Seq.empty[PIdnDef]).map(_.name).toSet
      val freeVars = mutable.Set.empty[String]

      case class BoundedVars(boundedVars: Set[String] = Set())
      StrategyBuilder.ContextVisitor[PNode, BoundedVars](
      {
        case (id: PIdnUse, ctx) => freeVars ++= Set(id.name) -- ctx.c.boundedVars
          ctx
        case (q @ (_: PForall | _: PExists), ctx) => ctx.updateContext(ctx.c.copy(boundedVars = ctx.c.boundedVars |
          q.asInstanceOf[PQuantifier].vars.map(_.idndef.name).toSet))
        case (_, c) => c
      }, BoundedVars()).execute(define)

      val nonUsedParameter = parameters -- freeVars

      if (nonUsedParameter.nonEmpty) {
        Seq(ParseWarning(s"In macro ${define.idndef.name}, the following parameters were defined but not used: " +
          s"${nonUsedParameter.mkString(", ")} ", SourcePosition(_file, define.pos._1.asInstanceOf[FilePosition].line, define.pos._1.asInstanceOf[FilePosition].column)))
      }
      else
        Seq()
    }

    var warnings = Seq.empty[ParseWarning]

    warnings = globalMacros.foldLeft(warnings)(_ ++ allParametersUsedInBody(_))

    globalMacros.foreach(allParametersUsedInBody(_))

    // Expand defines
    val domains =
      p.domains.map(domain => {
        doExpandDefines[PDomain](globalMacros, domain, p)
      })

    val functions =
      p.functions.map(function => {
        doExpandDefines(globalMacros, function, p)
      })

    val predicates =
      p.predicates.map(predicate => {
        doExpandDefines(globalMacros, predicate, p)
      })

    def linearizeMethod(method: PMethod): PMethod = {
      def linearizeSeqOfNestedStmt(pseqn: PSeqn): Seq[PStmt] = {
        var stmts = Seq.empty[PStmt]
        pseqn.ss.foreach {
          case s: PSeqn => stmts = stmts ++ linearizeSeqOfNestedStmt(s)
          case v => stmts = stmts :+ v
        }
        stmts
      }

      val body = method.body match {
        case Some(s: PSeqn) => Some(PSeqn(linearizeSeqOfNestedStmt(s))(method.pos))
        case v => v
      }

      if (body != method.body) {
        PMethod(method.idndef, method.formalArgs, method.formalReturns, method.pres, method.posts, body)(method.pos)
      } else {
        method
      }
    }

    val methods = p.methods.map(method => {
      // Collect local macro definitions
      val localMacros = method.deepCollect { case n: PDefine => n }

      warnings = localMacros.foldLeft(warnings)(_ ++ allParametersUsedInBody(_))

      // Remove local macro definitions from method
      val methodWithoutMacros =
        if (localMacros.isEmpty)
          method
        else
          method.transform { case mac: PDefine => PSkip()(mac.pos) }()

      linearizeMethod(doExpandDefines(localMacros ++ globalMacros, methodWithoutMacros, p))
    })

    PProgram(p.imports, p.macros, domains, p.fields, functions, predicates, methods, p.extensions, p.errors ++ warnings)(p.pos)
  }


  /**
    * Expand all macro calls in a subtree of the program's AST
    *
    * @param macros   All macros that can be called in the subtree
    * @param subtree  The root the subtree whose macro calls will be expanded
    * @param program  Root of the AST representing the program which includes 'subtree'
    * @tparam T       Type parameter of 'subtree' and return type, which is a subtype of PNode
    * @return         The same subtree with all macro calls expanded
    */
  def doExpandDefines[T <: PNode] (macros: Seq[PDefine], subtree: T, program: PProgram): T = {

    // Store the replacements from normal variable to freshly generated variable
    val renamesMap = mutable.Map.empty[String, String]
    var scopeAtMacroCall = Set.empty[String]
    val scopeOfExpandedMacros = mutable.Set.empty[String]

    def scope: Set[String] = scopeAtMacroCall ++ scopeOfExpandedMacros

    case class ReplaceContext(paramToArgMap: Map[String, PExp] = Map.empty,
                              boundVars: Set[String] = Set.empty)

    // Handy method to get a macro from its name string
    def getMacroByName(name: String): PDefine = macros.find(_.idndef.name == name) match {
      case Some(mac) => mac
      case None => throw ParseException(s"Macro " + name + " used but not present in scope", NoPosition) //? String is not a node, fix this.
    }

    // Check if a string is a valid macro name
    def isMacro(name: String): Boolean = macros.exists(_.idndef.name == name)

    object getFreshVarName {
      private val namesToNumbers = mutable.Map.empty[String, Int]

      def apply(name: String): String = {
        var number = namesToNumbers.get(name) match {
          case Some(number) => number + 1
          case None => 0
        }

        val freshVarName = (name: String, number: Int) => s"$name$$$number"

        while (scope.contains(freshVarName(name, number)))
          number += 1

        namesToNumbers += name -> number

        freshVarName(name, number)
      }
    }

    // Create a map that maps the formal parameters to the actual arguments of a macro call
    def mapParamsToArgs(params: Seq[PIdnDef], args: Seq[PExp]): Map[String, PExp] = {
      params.map(_.name).zip(args).toMap
    }

    /* Abstraction over several possible `PNode`s that can represent macro applications */
    case class MacroApp(name: String, arguments: Seq[PExp], node: PNode)

    val matchOnMacroCall: PartialFunction[PNode, MacroApp] = {
      case app: PMacroRef => MacroApp(app.idnuse.name, Nil, app)
      case app@PAssign(_, call: PCall) if isMacro(call.func.name) => MacroApp(call.func.name, call.args, app)
      case app: PCall if isMacro(app.func.name) => MacroApp(app.func.name, app.args, app)
      case app: PIdnUse if isMacro(app.name) => MacroApp(app.name, Nil, app)
    }

    def detectCyclicMacros(start: PNode, seen: Set[String]): Unit = {
      start.visit(
        matchOnMacroCall.andThen { case MacroApp(name, _, _) =>
          if (seen.contains(name)) {
            val position =
              macros.find(_.idndef.name == name)
                    .fold[Position](NoPosition)({ d: PDefine => d.pos._1 })

            throw ParseException("Recursive macro declaration found: " + name, position)
          } else {
            detectCyclicMacros(getMacroByName(name).body, seen + name)
          }
        }
      )
    }

    detectCyclicMacros(subtree, Set.empty)

    // Strategy to rename variables declared in macro's body if their names are already used in
    // the scope where the macro is being expanded, avoiding name clashes (hygienic macro expansion)
    val renamer = StrategyBuilder.Slim[PNode]({

      // Variable declared: either local or bound
      case varDecl: PIdnDef =>

        // If variable name is already used in scope
        if (scope.contains(varDecl.name)) {

          // Rename variable
          val freshVarName = getFreshVarName(varDecl.name)

          // Update scope
          scopeOfExpandedMacros += freshVarName
          renamesMap += varDecl.name -> freshVarName

          // Create a variable with new name to substitute the previous one
          val freshVarDecl = PIdnDef(freshVarName)(varDecl.pos)

          freshVarDecl
        } else {

          // Update scope
          scopeOfExpandedMacros += varDecl.name

          // Return the same variable
          varDecl
        }

      // Variable used: update variable's name according to its declaration
      // Macro's parameters are not renamed, since they will be replaced by
      // their respective arguments in the following steps (by replacer)
      case varUse: PIdnUse if renamesMap.contains(varUse.name) =>
        PIdnUse(renamesMap(varUse.name))(varUse.pos)
    })

    // Strategy to replace macro's parameters by their respective arguments
    val replacer = StrategyBuilder.Context[PNode, ReplaceContext]({

      // Variable use: macro parameters are replaced by their respective argument expressions
      case (varUse: PIdnUse, ctx) if ctx.c.paramToArgMap.contains(varUse.name) &&
                                     !ctx.c.boundVars.contains(varUse.name) =>
        (ctx.c.paramToArgMap(varUse.name), ctx.updateContext(ctx.c.copy(paramToArgMap = ctx.c.paramToArgMap.empty)))

      case (q @ (_: PForall | _: PExists), ctx) =>
        (q, ctx.updateContext(ctx.c.copy(boundVars = ctx.c.boundVars | q.asInstanceOf[PQuantifier].vars.map(_.idndef.name).toSet)))
    }, ReplaceContext())

    // The position of every node inside the macro is the position where the macro is "called"
    def adaptPositions(body: PNode, pos: (Position, Position)): PNode = {
      val children = body.children.map { child => if (child.isInstanceOf[PNode]) adaptPositions(child.asInstanceOf[PNode], pos) else child}
      body.withChildren(children, Some(pos))
    }

    // Replace variables in macro body, adapt positions correctly (same line number as macro call)
    def replacerOnBody(body: PNode, paramToArgMap: Map[String, PExp], pos: (Position, Position)): PNode = {

      // Duplicate the body of the macro to allow for differing type checks depending on the context
      val replicatedBody = body.deepCopyAll

      // Rename locally bound variables in macro's body
      var bodyWithRenamedVars = renamer.execute[PNode](replicatedBody)
      bodyWithRenamedVars = adaptPositions(bodyWithRenamedVars, pos)

      // Create context
      val context = new PartialContextC[PNode, ReplaceContext](ReplaceContext(paramToArgMap))

      // Replace macro's call arguments for every occurrence of its respective parameters in the body
      var bodyWithReplacedParams = replacer.execute[PNode](bodyWithRenamedVars, context)
      bodyWithReplacedParams = adaptPositions(bodyWithReplacedParams, pos)

      // Return expanded macro's body
      bodyWithReplacedParams
    }

    def ExpandMacroIfValid(macroCall: PNode, ctx: ContextA[PNode]): PNode = {
      matchOnMacroCall.andThen {
        case MacroApp(name, arguments, call) =>
          val macroDefinition = getMacroByName(name)
          val parameters = macroDefinition.parameters.getOrElse(Nil)
          val body = macroDefinition.body

          if (arguments.length != parameters.length)
            throw ParseException("Number of macro arguments does not match", call.pos._1)

          (call, body) match {
            case (_: PStmt, _: PExp) =>
              throw ParseException("Expression macro used in statement position", call.pos._1)
            case (_: PExp, _: PStmt) =>
              throw ParseException("Statement macro used in expression position", call.pos._1)
            case _ =>
          }

          /* TODO: The current unsupported position detection is probably not exhaustive.
           *       Seems difficult to concisely and precisely match all (il)legal cases, however.
           */
          (ctx.parent, body) match {
            case (PAccPred(loc, _), _) if (loc eq call) && !body.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, call.pos._1)
            case (_: PCurPerm, _) if !body.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, call.pos._1)
            case _ => /* All good */
          }

          try {
            scopeAtMacroCall = NameAnalyser().namesInScope(program, Some(macroCall))
            arguments.foreach(
              StrategyBuilder.SlimVisitor[PNode] {
                case id: PIdnDef => scopeAtMacroCall += id.name
                case _ =>
              }.execute[PNode](_)
            )
            StrategyBuilder.SlimVisitor[PNode]({
              case id: PIdnDef => scopeAtMacroCall += id.name
              case _ =>
            }).execute(subtree)
            renamesMap.clear()
            replacerOnBody(body, mapParamsToArgs(parameters, arguments), call.pos)
          } catch {
            case problem: ParseTreeDuplicationError =>
              throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, call.pos._1)
          }
      }.applyOrElse(macroCall, (_: PNode) => macroCall)
    }

    // Strategy that checks if the macro calls are valid and expands them.
    // Requires that macro calls are acyclic
    val expander = StrategyBuilder.Ancestor[PNode] {

      // Handles macros on the left hand-side of assignments
      case (assign@PAssign(targets, rhs), ctx) =>
        val expandedTargets = targets map {
          case call: PCall => {
            if (!isMacro(call.opName))
              throw ParseException("The only calls that can be on the left-hand side of an assignment statement are calls to macros", call.pos._1)
            val body = ExpandMacroIfValid(call, ctx)

            // Check if macro's body can be the left-hand side of an assignment and,
            // if that's the case, add it in a corresponding assignment statement
            body match {
              case target: PAssignTarget => target
              case _ => throw ParseException("The body of this macro is not a suitable left-hand side for an assignment statement", call.pos._1)
            }
          }
          case target => target
        }
        val expandedLhs = PAssign(expandedTargets, rhs)(assign.pos)
        (ExpandMacroIfValid(expandedLhs, ctx), ctx)

      // Handles all other calls to macros
      case (node, ctx) => (ExpandMacroIfValid(node, ctx), ctx)

    }.recurseFunc {
      /* Don't recurse into the PIdnUse of nodes that themselves could represent macro
       * applications. Otherwise, the expansion of nested macros will fail due to attempting
       * to construct invalid AST nodes.
       * Recursing into such PIdnUse nodes caused Silver issue #205.
       */
      case PMacroRef(_) => Seq.empty
      case PCall(_, args, typeAnnotated) => Seq(args, typeAnnotated)
    }.repeat

    try {
      expander.execute[T](subtree)
    } catch {
      case problem: ParseTreeDuplicationError =>
        throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, problem.original.pos._1)
    }
  }

  /** The file we are currently parsing (for creating positions later). */
  def file: Path = _file

  lazy val keywords = FastParserCompanion.basicKeywords | ParserExtension.extendedKeywords

  // Note that `typedFapp` is before `"(" ~ exp ~ ")"` to ensure that the latter doesn't gobble up the brackets for the former
  // and then look like an `fapp` up untill the `: type` part, after which we need to backtrack all the way back (or error if cut)
  def atom(implicit ctx : P[_]) : P[PExp] = P(ParserExtension.newExpAtStart(ctx) | integer | booltrue | boolfalse | nul | old
    | result | unExp | typedFapp
    | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
    | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
    | size | explicitSeqNonEmpty | seqRange
    | mapTypedEmpty | explicitMapNonEmpty | mapDomain | mapRange
    | newExp | fapp | idnuse | ParserExtension.newExpAtEnd(ctx))

  def result[$: P]: P[PResultLit] = FP(keyword("result")).map { case (pos, _) => PResultLit()(pos) }

  def unExp[$: P]: P[PUnExp] = FP(CharIn("\\-\\!").! ~ suffixExpr).map { case (pos, (a, b)) => PUnExp(a, b)(pos) }

  def strInteger[$: P]: P[String] = P(CharIn("0-9").rep(1)).!

  def integer[$: P]: P[PIntLit] = FP(strInteger.filter(s => s.matches("\\S+"))).map { case (pos, s) => PIntLit(BigInt(s))(pos) }

  def booltrue[$: P]: P[PBoolLit] = FP(keyword("true")).map {case (pos, _) => PBoolLit(b = true)(pos)}

  def boolfalse[$: P]: P[PBoolLit] = FP(keyword("false")).map{ case (pos, _) => PBoolLit(b = false)(pos) }

  def nul[$: P]: P[PNullLit] = FP(keyword("null")).map { case (pos, _) => PNullLit()(pos) }

  def identifier[$: P]: P[Unit] = CharIn("A-Z", "a-z", "$_") ~~ CharIn("0-9", "A-Z", "a-z", "$_").repX

  def ident[$: P]: P[String] = identifier.!.filter(a => !keywords.contains(a)).opaque("invalid identifier (could be a keyword)")

  def idnuse[$: P]: P[PIdnUse] = FP(ident).map { case (pos, id) => PIdnUse(id)(pos) }

  def oldLabel[$: P]: P[PIdnUse] = idnuse | FP(LabelledOld.LhsOldLabel.!).map {
    case (pos, lhsOldLabel) => PIdnUse(lhsOldLabel)(pos)
  }

  def old[$: P]: P[PExp] = P(StringIn("old") ~ (FP(parens(exp)).map { case (pos, e) => POld(e)(pos) } | FP("[" ~ oldLabel ~ "]" ~ parens(exp)).map {
    case (pos, (a, b)) => PLabelledOld(a, b)(pos)
  }))

  def magicWandExp[$: P]: P[PExp] = FP(orExp ~~~ (keyword("--*").! ~ exp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PMagicWandExp(a, c._2)(pos)
      case None => a
  }}

  def realMagicWandExp[$: P]: P[PMagicWandExp] = FP(orExp ~ "--*" ~ exp).map {
    case (pos, (a, b)) => PMagicWandExp(a, b)(pos)
  }

  def implExp[$: P]: P[PExp] = FP(magicWandExp ~~~ (StringIn("==>").! ~ implExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def iffExp[$: P]: P[PExp] = FP(implExp ~~~ ("<==>".! ~ iffExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def iteExpr[$: P]: P[PExp] = FP(iffExp ~~~ ("?" ~ iteExpr ~ ":" ~ iteExpr).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PCondExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def exp[$: P]: P[PExp] = P(iteExpr)

  def suffix[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(FP("." ~ idnuse).map { case (pos, id) => SuffixedExpressionGenerator[PExp]((e: PExp) => PFieldAccess(e, id)(pos)) } |
      FP("[" ~ Pass ~ ".." ~/ exp ~ "]").map { case (pos, n) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqTake(e, n)(pos)) } |
      FP("[" ~ exp ~ ".." ~ Pass ~ "]").map { case (pos, n) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(e, n)(pos)) } |
      FP("[" ~ exp ~ ".." ~ exp ~ "]").map { case (pos, (n, m)) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(PSeqTake(e, m)(pos), n)(pos)) } |
      FP("[" ~ exp ~ "]").map { case (pos, e1) => SuffixedExpressionGenerator[PExp]((e0: PExp) => PLookup(e0, e1)(pos)) } |
      FP("[" ~ exp ~ ":=" ~ exp ~ "]").map { case (pos, (i, v)) => SuffixedExpressionGenerator[PExp]((e: PExp) => PUpdate(e, i, v)(pos)) })

  /*
  Maps:
  def suffix[$: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(FP("." ~ idnuse).map { case (pos, id) => SuffixedExpressionGenerator[PExp]((e: PExp) => {
      PFieldAccess(e, id)(pos)
    }) } |
      FP("[" ~ Pass ~ ".." ~/ exp ~ "]").map { case (pos, n) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqTake(e, n)(pos)) } |
      FP("[" ~ exp ~ ".." ~ Pass ~ "]").map { case (pos, n) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(e, n)(pos)) } |
      FP("[" ~ exp ~ ".." ~ exp ~ "]").map { case (pos, (n, m)) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(PSeqTake(e, m)(), n)(pos)) } |
      FP("[" ~ exp ~ "]").map { case (pos, e1) => SuffixedExpressionGenerator[PExp]((e0: PExp) => PSeqIndex(e0, e1)(pos)) } |
      FP("[" ~ exp ~ ":=" ~ exp ~ "]").map { case (pos, (i, v)) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqUpdate(e, i, v)(pos)) })
   */

  def suffixExpr[$: P]: P[PExp] = P((atom ~~~ suffix.lw.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  def termOp[$: P]: P[String] = P(StringIn("*", "/", "\\", "%").!)

  def term[$: P]: P[PExp] = P((suffixExpr ~~~ termd.lw.rep).map { case (a, ss) => foldPExp[PExp](a, ss) })

  def termd[$: P]: P[SuffixedExpressionGenerator[PExp]] = FP(termOp ~ suffixExpr).map { case (pos, (op, id)) => SuffixedExpressionGenerator[PExp]((e: PExp) => PBinExp(e, op, id)(pos)) }

  def sumOp[$: P]: P[String] = P(StringIn("++", "+", "-").! | keyword("union").! | keyword("intersection").! | keyword("setminus").! | keyword("subset").!)

  def sum[$: P]: P[PExp] = P((term ~~~ sumd.lw.rep).map { case (a, ss) => foldPExp[PBinExp](a, ss) })

  def sumd[$: P]: P[SuffixedExpressionGenerator[PBinExp]] = FP(sumOp ~ term).map { case (pos, (op, id)) => SuffixedExpressionGenerator[PBinExp]((e: PExp) => PBinExp(e, op, id)(pos)) }

  def cmpOp[$: P] = P(StringIn("<=", ">=", "<", ">").! | keyword("in").!)

  def cmpExp[$: P]: P[PExp] = FP(sum ~~~ (cmpOp ~ cmpExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def eqOp[$: P] = P(StringIn("==", "!=").!)

  def eqExp[$: P]: P[PExp] = FP(cmpExp ~~~ (eqOp ~ eqExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def andExp[$: P]: P[PExp] = FP(eqExp ~~~ ("&&".! ~ andExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def orExp[$: P]: P[PExp] = FP(andExp ~~~ ("||".! ~ orExp).lw.?).map {
    case (pos, (a, b)) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)(pos)
      case None => a
    }
  }

  def accessPredImpl[$: P]: P[PAccPred] = FP(keyword("acc") ~ "(" ~ locAcc ~ ("," ~ exp).? ~ ")").map {
    case (pos, (loc, perms)) => {
      PAccPred(loc, perms.getOrElse(PFullPerm()(pos)))(pos)
    }
  }

  def accessPred[$: P]: P[PAccPred] = accessPredImpl

  def resAcc[$: P]: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  def locAcc[$: P]: P[PLocationAccess] = P(fieldAcc | predAcc)

  def fieldAcc[$: P]: P[PFieldAccess] =
    P(NoCut(suffixExpr.filter(isFieldAccess)).map {
      case fa: PFieldAccess => fa
      case other => sys.error(s"Unexpectedly found $other")
    })

  def predAcc[$: P]: P[PLocationAccess] = fapp

  def actualArgList[$: P]: P[Seq[PExp]] = exp.rep(sep = ",")

  def inhaleExhale[$: P]: P[PExp] = FP("[" ~ exp ~ "," ~ exp ~ "]").map {
    case (pos, (a, b)) => PInhaleExhaleExp(a, b)(pos)
  }

  def perm[$: P]: P[PExp] =
    P(FP(keyword("none")).map{ case (pos, _) => PNoPerm()(pos)} |
      FP(keyword("wildcard")).map{ case (pos, _) => PWildcard()(pos)} |
      FP(keyword("write")).map{ case (pos, _) => PFullPerm()(pos)} |
      FP(keyword("epsilon")).map{ case (pos, _) => PEpsilon()(pos)} |
      FP("perm" ~ parens(resAcc)).map{ case (pos, r) => PCurPerm(r)(pos)})

  def let[$: P]: P[PExp] =
    FP("let" ~/ FP(idndef) ~ "==" ~ "(" ~ exp ~ ")" ~ "in" ~ FP(exp)).map {
      case (pos, (idpos, id, exp1, (e2pos, exp2))) =>
      /* Type unresolvedType is expected to be replaced with the type of exp1
       * after the latter has been resolved
       * */
      val unresolvedType = PUnknown()(idpos)
      val formalArgDecl = PFormalArgDecl(id, unresolvedType)(idpos)
      val nestedScope = PLetNestedScope(formalArgDecl, exp2)(e2pos)

      PLet(exp1, nestedScope)(pos)
    }

  def idndef[$: P]: P[PIdnDef] = FP(ident).map {
    case (pos, s) =>
      PIdnDef(s)(pos)
    }

  def quant[$: P]: P[PExp] = P(FP(keyword("forall") ~ nonEmptyFormalArgList ~ "::" ~ trigger.rep ~ exp).map {
    case (pos, (a, b, c)) =>
      PForall(a, b, c)(pos)
    } |
    FP(keyword("exists") ~ nonEmptyFormalArgList ~ "::" ~ trigger.rep ~ exp).map {
      case (pos, (a, b, c)) =>
        PExists(a, b, c)(pos)
    })

  def nonEmptyFormalArgList[$: P]: P[Seq[PFormalArgDecl]] = P(formalArg.rep(min = 1, sep = ","))

  def formalArg[$: P]: P[PFormalArgDecl] = FP(idndef ~ ":" ~ typ).map { case (pos, (a, b)) => PFormalArgDecl(a, b)(pos) }

  def typ[$: P]: P[PType] = P(primitiveTyp | domainTyp | seqType | setType | multisetType | mapType)
  // Maps: lazy val typ: P[PType] = P(primitiveTyp | domainTyp | seqType | setType | multisetType | mapType)

  def domainTyp[$: P]: P[PDomainType] = P(FP(idnuse ~ "[" ~ typ.rep(sep = ",") ~ "]").map { case (pos, (a, b)) => PDomainType(a, b)(pos) } |
    // domain type without type arguments (might also be a type variable)
    idnuse.map(name => {
      PDomainType(name, Nil)(name.pos)
    }))

  def seqType[$: P]: P[PType] = FP(keyword("Seq") ~ "[" ~ typ ~ "]").map{ case (pos, t) => PSeqType(t)(pos)}

  def setType[$: P]: P[PType] = FP(keyword("Set") ~ "[" ~ typ ~ "]").map{ case (pos, t) => PSetType(t)(pos)}

  def multisetType[$: P]: P[PType] = FP(keyword("Multiset") ~ "[" ~ typ ~ "]").map{ case (pos, t) => PMultisetType(t)(pos)}

  //def mapType[$: P]: P[PType] = FP(keyword("Map") ~ "[" ~ typ ~ "," ~ typ ~ "]").map{ case (pos, t) => PSeqType(t._3)(pos)}
  // Maps:
  def mapType[$: P] : P[PType] = FP(keyword("Map") ~ "[" ~ typ ~ "," ~ typ ~ "]").map {
   case (pos, (keyType, valueType)) => PMapType(keyType, valueType)(pos)
  }

  def primitiveTyp[$: P]: P[PType] = P(FP(keyword("Rational")).map{ case (pos, _) => PPrimitiv("Perm")(pos)}
    | FP((StringIn("Int", "Bool", "Perm", "Ref") ~~ !identContinues).!).map{ case (pos, name) => PPrimitiv(name)(pos)})
/* Maps:
  lazy val primitiveTyp: P[PType] = P(keyword("Rational").map(_ => PPrimitiv("Perm"))
    | (StringIn("Int", "Bool", "Perm", "Ref") ~~ !identContinues).!.map(PPrimitiv))
 */

  def trigger[$: P]: P[PTrigger] = FP("{" ~/ exp.rep(sep = ",") ~ "}").map{
    case (pos, s) => PTrigger(s)(pos)
  }

  def forperm[$: P]: P[PExp] = FP(keyword("forperm") ~ nonEmptyFormalArgList ~ "[" ~ resAcc ~ "]" ~ "::" ~ exp).map {
    case (pos, (args, res, body)) => PForPerm(args, res, body)(pos)
  }

  def unfolding[$: P]: P[PExp] = FP(keyword("unfolding") ~ predicateAccessPred ~ "in" ~ exp).map {
    case (pos, (a, b)) => PUnfolding(a, b)(pos) }

  def predicateAccessPred[$: P]: P[PAccPred] = P(accessPred | FP(predAcc).map {
    case (pos, loc) => PAccPred(loc, PFullPerm()(pos))(pos)
  })

  def setTypedEmpty[$: P]: P[PExp] = collectionTypedEmpty("Set", (a, b) => PEmptySet(a)(b))

  def explicitSetNonEmpty[$: P]: P[PExp] = P(FP("Set" ~ "(" ~ exp.rep(sep = ",", min = 1) ~ ")").map {
    case (pos, exps) => PExplicitSet(exps)(pos)
  })

  def explicitMultisetNonEmpty[$: P]: P[PExp] = P(FP("Multiset" ~ "(" ~ exp.rep(min = 1, sep = ",") ~ ")").map {
    case (pos, exps) => PExplicitMultiset(exps)(pos)
  })

  def multiSetTypedEmpty[$: P]: P[PExp] = collectionTypedEmpty("Multiset", (a, b) => PEmptyMultiset(a)(b))

  def seqTypedEmpty[$: P]: P[PExp] = collectionTypedEmpty("Seq", (a, b) => PEmptySeq(a)(b))

  def size[$: P]: P[PExp] = P(FP("|" ~ exp ~ "|").map {
    case (pos, e) => PSize(e)(pos)
  })

  def explicitSeqNonEmpty[$: P]: P[PExp] = P(FP("Seq" ~ "(" ~ exp.rep(min = 1, sep = ",") ~ ")").map {
    case (pos, exps) => PExplicitSeq(exps)(pos)
  })

  private def collectionTypedEmpty[$: P](name: String, typeConstructor: (PType, (Position, Position)) => PExp): P[PExp] =
    FP(`name` ~ ("[" ~ typ ~ "]").? ~ "(" ~ ")").map{ case (pos, typ) => typeConstructor(typ.getOrElse(PTypeVar("#E")), pos)}

  def seqRange[$: P]: P[PExp] = FP("[" ~ exp ~ ".." ~ exp ~ ")").map { case (pos, (a, b)) => PRangeSeq(a, b)(pos) }

  def mapTypedEmpty[$: P] : P[PMapLiteral] = P(FP("Map" ~ ("[" ~ typ ~ "," ~ typ ~ "]").? ~ "(" ~ ")").map {
    case (pos, Some((keyType, valueType))) => PEmptyMap(keyType, valueType)(pos)
    case (pos, None) => PEmptyMap(PTypeVar("#K"), PTypeVar("#E"))(pos)
  })

  def maplet[$: P]: P[PMaplet] = P(FP(exp ~ ":=" ~ exp).map {
    case (pos, (key, value)) => PMaplet(key, value)(pos)
  })

  def explicitMapNonEmpty[$: P]: P[PMapLiteral] = P(FP("Map" ~ "(" ~ maplet.rep(sep = ",", min = 1) ~ ")").map {
    case (pos, maplets) => PExplicitMap(maplets)(pos)
  })

  def mapDomain[$: P]: P[PExp] = P(FP("domain" ~ "(" ~ exp ~ ")").map {
    case (pos, e) => PMapDomain(e)(pos)
  })

  def mapRange[$: P] : P[PExp] = P(FP("range" ~ "(" ~ exp ~ ")").map {
    case (pos, e) => PMapRange(e)(pos)
  })

  def newExp[$: P]: P[PNewExp] = FP("new" ~ "(" ~ newExpFields ~ ")").map { case (pos, fields) => PNewExp(fields)(pos) }

  def newExpFields[$: P]: P[Option[Seq[PIdnUse]]] = P(P("*").map(_ => None) | P(idnuse.rep(sep = ",")).map(Some(_)))

  def fapp[$: P]: P[PCall] = FP(idnuse ~ parens(actualArgList)).map {
    case (pos, (func, args)) =>
      PCall(func, args, None)(pos)
  }

  def typedFapp[$: P]: P[PExp] = FP(parens(idnuse ~ parens(actualArgList) ~ ":" ~ typ)).map {
    case (pos, (func, args, typeGiven)) => PCall(func, args, Some(typeGiven))(pos)
  }

  def stmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | fold | unfold | exhale | assertP |
    inhale | assume | ifthnels | whle | varDecl | defineDecl | 
    goto | lbl | packageWand | applyWand | assign | macroref | block |
    quasihavoc | quasihavocall | ParserExtension.newStmtAtEnd(ctx))

  def nodefinestmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | fold | unfold | exhale | assertP |
    inhale | assume | ifthnels | whle | varDecl |
    goto | lbl | packageWand | applyWand | assign | macroref | block |
    quasihavoc | quasihavocall | ParserExtension.newStmtAtEnd(ctx))

  def macroref[$: P]: P[PMacroRef] = FP(idnuse).map { case (pos, a) => PMacroRef(a)(pos) }

  def assignTarget[$: P]: P[PAssignTarget] = P(fieldAcc | NoCut(fapp) | idnuse)

  def assign[$: P]: P[PAssign] = FP((assignTarget.rep(min = 1, sep = ",") ~ ":=").? ~ exp).map { case (pos, (targets, rhs)) => PAssign(targets.getOrElse(Seq()), rhs)(pos) }

  def fold[$: P]: P[PFold] = FP("fold" ~ predicateAccessPred).map{ case (pos, e) => PFold(e)(pos)}

  def unfold[$: P]: P[PUnfold] = FP("unfold" ~ predicateAccessPred).map{ case (pos, e) => PUnfold(e)(pos)}

  def exhale[$: P]: P[PExhale] = FP(keyword("exhale") ~/ exp).map{ case (pos, e) => PExhale(e)(pos) }

  def assertP[$: P]: P[PAssert] = FP(keyword("assert") ~/ exp).map{ case (pos, e) => PAssert(e)(pos) }

  def inhale[$: P]: P[PInhale] = FP(keyword("inhale") ~/ exp).map{ case (pos, e) => PInhale(e)(pos) }

  def assume[$: P]: P[PAssume] = FP(keyword("assume") ~/ exp).map{ case (pos, e) => PAssume(e)(pos) }

  // Parsing Havoc statements
  // Havoc statements have two forms:
  //    1. havoc <resource>
  //    2. havoc <exp> ==> <resource>
  // Note that you cannot generalize (2) to something like "<exp1> ==> <exp2> ==> <resource>".
  // We therefore forbid the lhs of (2) from being an arbitrary expression. Instead,
  // we enforce that it's a "magicWandExp", which is one level below an implication expression
  // in the grammar. Note that it is still possible to express "(<exp1> ==> <exp2>) ==> <resource>
  // using parentheses.

  // Havocall follows a similar pattern to havoc but allows quantifying over variables.

  def quasihavoc[$: P]: P[PQuasihavoc] = FP(keyword("quasihavoc") ~/
    (magicWandExp ~ "==>").? ~ exp ).map {
      case (pos, (lhs, rhs)) => PQuasihavoc(lhs, rhs)(pos)
  }

  def quasihavocall[$: P]: P[PQuasihavocall] = FP(keyword("quasihavocall") ~/
    nonEmptyFormalArgList ~ "::" ~ (magicWandExp ~ "==>").? ~ exp).map {
    case (pos, (vars, lhs, rhs)) => PQuasihavocall(vars, lhs, rhs)(pos)
  }

  def ifthnels[$: P]: P[PIf] = FP("if" ~ "(" ~ exp ~ ")" ~ block ~~~ elsifEls).map {
    case (pos, (cond, thn, ele)) => PIf(cond, thn, ele)(pos)
  }

  // No need for `.lw` here since we have `FP("{" ~ ... ~ "}")`
  def block[$: P]: P[PSeqn] = FP("{" ~/ (stmt ~/ ";".?).rep ~ "}").map{ case (pos, e) => PSeqn(e)(pos)}

  def elsifEls[$: P]: LW[PSeqn] = elsif.lw | els

  def elsif[$: P]: P[PSeqn] = FP("elseif" ~/ "(" ~ exp ~ ")" ~ block ~~~ elsifEls).map {
    case (pos, (cond, thn, ele)) => PSeqn(Seq(PIf(cond, thn, ele)(pos)))(pos)
  }

  def els[$: P]: LW[PSeqn] = ((keyword("else") ~/ block) | FP(Pass).map {
    case (pos, _) => PSeqn(Nil)(pos)
  }).lw

  def whle[$: P]: P[PWhile] = FP(keyword("while") ~/ "(" ~ exp ~ ")" ~ inv.rep ~ block).map {
    case (pos, (cond, invs, body)) =>
      PWhile(cond, invs, body)(pos)
  }

  def inv(implicit ctx : P[_]) : P[PExp] = P((keyword("invariant") ~ exp ~~~ ";".lw.?) | ParserExtension.invSpecification(ctx))

  def varDecl[$: P]: P[PLocalVarDecl] = FP(keyword("var") ~/ nonEmptyFormalArgList ~~~ (":=" ~ exp).lw.?).map {
    case (pos, (a, b)) => PLocalVarDecl(a, b.map(i => PAssign(a.map(v => PIdnUse(v.idndef.name)(v.idndef.pos)), i)(pos)))(pos)
  }

  def defineDecl[$: P]: P[PDefine] = FP(keyword("define") ~/ idndef ~ ("(" ~ idndef.rep(sep = ",") ~ ")").? ~ (exp | "{" ~ (nodefinestmt ~ ";".?).rep ~ "}")).map {
    case (pos, (a, b, c)) => c match {
      case e: PExp => PDefine(a, b, e)(pos)
      case ss: Seq[PStmt]@unchecked => PDefine(a, b, PSeqn(ss)(pos))(pos)
    }
  }

  def goto[$: P]: P[PGoto] = FP("goto" ~/ idnuse).map{ case (pos, e) => PGoto(e)(pos) }

  def lbl[$: P]: P[PLabel] = FP(keyword("label") ~/ idndef ~~~ (keyword("invariant") ~/ exp).lw.rep).map {
    case (pos, (name, invs)) => PLabel(name, invs)(pos) }

  def packageWand[$: P]: P[PPackageWand] = FP(keyword("package") ~/ magicWandExp ~~~ block.lw.?).map {
    case (pos, (wand, Some(proofScript))) =>
      PPackageWand(wand, proofScript)(pos)
    case (pos, (wand, None)) =>
      PPackageWand(wand, PSeqn(Seq())(pos))(pos)
  }

  def applyWand[$: P]: P[PApplyWand] = FP(keyword("apply") ~/ magicWandExp).map {
    case (pos, p) => PApplyWand(p)(pos)
  }

  def applying[$: P]: P[PExp] = FP(keyword("applying") ~/ "(" ~ magicWandExp ~ ")" ~ "in" ~ exp).map { case (pos, (a, b)) => PApplying(a, b)(pos) }

  def programDecl(implicit ctx : P[_]) : P[PProgram] = P(FP((ParserExtension.newDeclAtStart(ctx) | preambleImport | defineDecl | domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl | ParserExtension.newDeclAtEnd(ctx)).rep).map {
    case (pos, decls) => {
      PProgram(
        decls.collect { case i: PImport => i }, // Imports
        decls.collect { case d: PDefine => d }, // Macros
        decls.collect { case d: PDomain => d }, // Domains
        decls.collect { case f: PField => f }, // Fields
        decls.collect { case f: PFunction => f }, // Functions
        decls.collect { case p: PPredicate => p }, // Predicates
        decls.collect { case m: PMethod => m }, // Methods
        decls.collect { case e: PExtender => e }, // Extensions
        Seq() // Parse Errors
      )(pos)
    }
  })

  def preambleImport[$: P]: P[PImport] = FP(keyword("import") ~/ (
      P(quoted(relativeFilePath.!)).map{ filename => pos: (Position, Position) => PLocalImport(filename)(pos) } |
      P(angles(relativeFilePath.!)).map{ filename => pos: (Position, Position) => PStandardImport(filename)(pos) }
    )).map { case (pos, imp) => imp(pos) }

  def relativeFilePath[$: P]: P[String] = P(CharIn("~.").?.! ~~ (CharIn("/").? ~~ CharIn(".", "A-Z", "a-z", "0-9", "_\\- \n\t")).rep(1))

  def anyString[$: P]: P[String] = P(CharPred(c => c !='\"').rep(1).!)

  def domainDecl[$: P]: P[PDomain] = FP("domain" ~/ idndef ~ typeParams ~ ("interpretation" ~ parens((ident ~ ":" ~ quoted(anyString.!)).rep(sep = ","))).? ~ "{" ~ (domainFunctionDecl | axiomDecl).rep ~
    "}").map {
    case (pos, (name, typparams, interpretations, members)) =>
      val funcs = members collect { case m: PDomainFunction1 => m }
      val axioms = members collect { case m: PAxiom1 => m }
      PDomain(
        name,
        typparams,
        funcs map (f => PDomainFunction(f.idndef, f.formalArgs, f.typ, f.unique, f.interpretation)(PIdnUse(name.name)(name.pos))(f.pos)),
        axioms map (a => PAxiom(a.idndef, a.exp)(PIdnUse(name.name)(name.pos))(a.pos)),
        interpretations.map(i => i.toMap))(pos)
  }

  def domainTypeVarDecl[$: P]: P[PTypeVarDecl] = FP(idndef).map{ case (pos, i) => PTypeVarDecl(i)(pos) }

  def typeParams[$: P]: P[Seq[PTypeVarDecl]] = P(("[" ~ domainTypeVarDecl.rep(sep = ",") ~ "]").?).map(_.getOrElse(Nil))

  def domainFunctionDecl[$: P]: P[PDomainFunction1] = FP("unique".!.? ~ domainFunctionSignature ~ ("interpretation" ~ quoted(anyString.!)).? ~~~ ";".lw.?).map {
    case (pos, (unique, fdecl, interpretation)) => fdecl match {
      case (name, formalArgs, t) => PDomainFunction1(name, formalArgs, t, unique.isDefined, interpretation)(pos)
    }
  }

  def domainFunctionSignature[$: P] = P("function" ~ idndef ~ "(" ~ anyFormalArgList ~ ")" ~ ":" ~ typ)

  def anyFormalArgList[$: P]: P[Seq[PAnyFormalArgDecl]] = P((formalArg | unnamedFormalArg).rep(sep = ","))

  def unnamedFormalArg[$: P] = FP(typ).map{ case (pos, t) => PUnnamedFormalArgDecl(t)(pos) }

  def formalArgList[$: P]: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))

  def axiomDecl[$: P]: P[PAxiom1] = FP(keyword("axiom") ~ idndef.? ~ "{" ~ exp ~ "}" ~~~ ";".lw.?).map { case (pos, (a, b)) => PAxiom1(a, b)(pos) }

  def fieldDecl[$: P]: P[PField] = FP(keyword("field") ~/ idndef ~ ":" ~ typ ~~~ ";".lw.?).map {
    case (pos, (a, b)) => PField(a, b)(pos)
  }

  def functionDecl[$: P]: P[PFunction] = FP("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~~~ pre.lw.rep ~~~
    post.lw.rep ~~~ ("{" ~ exp ~ "}").lw.?).map({ case (pos, (a, b, c, d, e, f)) =>
      PFunction(a, b, c, d, e, f)(pos)
  })


  def pre(implicit ctx : P[_]) : P[PExp] = P(("requires" ~/ exp ~~~ ";".lw.?) | ParserExtension.preSpecification(ctx))

  def post(implicit ctx : P[_]) : P[PExp] = P(("ensures" ~/ exp ~~~ ";".lw.?) | ParserExtension.postSpecification(ctx))

  def decCl[$: P]: P[Seq[PExp]] = P(exp.rep(sep = ","))

  def predicateDecl[$: P]: P[PPredicate] = FP(keyword("predicate") ~/ idndef ~ "(" ~ formalArgList ~ ")" ~~~ ("{" ~ exp ~ "}").lw.?).map {
    case (pos, (a, b, c)) =>
      PPredicate(a, b, c)(pos)
  }

  def methodDecl[$: P]: P[PMethod] = FP(methodSignature ~~~/ pre.lw.rep ~~~ post.lw.rep ~~~ block.lw.?).map {
    case (pos, (name, args, rets, pres, posts, body)) =>
      PMethod(name, args, rets.getOrElse(Nil), pres, posts, body)(pos)
  }

  def methodSignature[$: P] = P("method" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~~~ ("returns" ~ "(" ~ formalArgList ~ ")").lw.?)

  def entireProgram[$: P]: P[PProgram] = P(Start ~ programDecl ~ End)


  object ParserExtension extends ParserPluginTemplate {

    import ParserPluginTemplate._

    /**
      * These private variables are the storage variables for each of the extensions.
      * As the parser are evaluated lazily, it is possible for us to stores extra parsing sequences in these variables
      * and after the plugins are loaded, the parsers are added to these variables and when any parser is required,
      * can be referenced back.
      */
    private var _newDeclAtEnd: Option[Extension[PExtender]] = None
    private var _newDeclAtStart: Option[Extension[PExtender]] = None

    private var _newExpAtEnd: Option[Extension[PExp]] = None
    private var _newExpAtStart: Option[Extension[PExp]] = None

    private var _newStmtAtEnd: Option[Extension[PStmt]] = None
    private var _newStmtAtStart: Option[Extension[PStmt]] = None

    private var _preSpecification: Option[Extension[PExp]] = None
    private var _postSpecification: Option[Extension[PExp]] = None
    private var _invSpecification: Option[Extension[PExp]] = None

    private var _extendedKeywords: Set[String] = Set()


    /**
      * For more details regarding the functionality of each of these initial parser extensions
      * and other hooks for the parser extension, please refer to ParserPluginTemplate.scala
      */
    override def newDeclAtStart : Extension[PExtender] = _newDeclAtStart match {
      case None => ParserPluginTemplate.defaultExtension
      case Some(ext) => ext
    }

    override def newDeclAtEnd : Extension[PExtender] = _newDeclAtEnd match {
      case None => ParserPluginTemplate.defaultExtension
      case Some(ext) => ext
    }

    override def newStmtAtEnd : Extension[PStmt] = _newStmtAtEnd match {
      case None => ParserPluginTemplate.defaultStmtExtension
      case Some(ext) => ext
    }

    override def newStmtAtStart : Extension[PStmt] = _newStmtAtStart match {
      case None => ParserPluginTemplate.defaultStmtExtension
      case Some(ext) => ext
    }

    override def newExpAtEnd : Extension[PExp] = _newExpAtEnd match {
      case None => ParserPluginTemplate.defaultExpExtension
      case Some(ext) => ext
    }

    override def newExpAtStart : Extension[PExp] = _newExpAtStart match {
      case None => ParserPluginTemplate.defaultExpExtension
      case Some(ext) => ext
    }

    override def postSpecification : Extension[PExp] = _postSpecification match {
      case None => ParserPluginTemplate.defaultExpExtension
      case Some(ext) => ext
    }

    override def preSpecification : Extension[PExp] = _preSpecification match {
      case None => ParserPluginTemplate.defaultExpExtension
      case Some(ext) => ext
    }

    override def invSpecification : Extension[PExp] = _invSpecification match {
      case None => ParserPluginTemplate.defaultExpExtension
      case Some(ext) => ext
    }

    override def extendedKeywords : Set[String] = _extendedKeywords

    def addNewDeclAtEnd(t: Extension[PExtender]) : Unit = _newDeclAtEnd match {
      case None => _newDeclAtEnd = Some(t)
      case Some(s) => _newDeclAtEnd = Some(combine(s, t))
    }

    def addNewDeclAtStart(t: Extension[PExtender]) : Unit = _newDeclAtStart match {
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

    def addNewPreCondition(t: Extension[PExp]) : Unit = _preSpecification match {
      case None => _preSpecification = Some(t)
      case Some(s) => _preSpecification = Some(combine(s, t))
    }

    def addNewPostCondition(t: Extension[PExp]) : Unit = _postSpecification match {
      case None => _postSpecification = Some(t)
      case Some(s) => _postSpecification = Some(combine(s, t))
    }

    def addNewInvariantCondition(t: Extension[PExp]) : Unit = _invSpecification match {
      case None => _invSpecification = Some(t)
      case Some(s) => _invSpecification = Some(combine(s, t))
    }

    def addNewKeywords(t : Set[String]) : Unit = {
      _extendedKeywords ++= t
    }
  }
}