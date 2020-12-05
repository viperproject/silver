// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.net.URL
import java.nio.file.{Files, Path, Paths}

import scala.util.parsing.input.{NoPosition, Position}  //?
import viper.silver.ast.{LabelledOld, LineCol, SourcePosition}
import viper.silver.FastPositions
import viper.silver.ast.utility.rewriter.{ContextA, PartialContextC, StrategyBuilder}
import viper.silver.parser.Transformer.ParseTreeDuplicationError
import viper.silver.plugin.SilverPluginManager
import viper.silver.verifier.{ParseError, ParseWarning}

import scala.collection.mutable


case class ParseException(msg: String, pos: scala.util.parsing.input.Position) extends Exception

case class SuffixedExpressionGenerator[E <: PExp](func: PExp => E) extends (PExp => PExp) with FastPositioned {
  override def apply(v1: PExp): E = func(v1)
}

object FastParser { // extends PosParser[Char, String] { //?
  import fastparse.{P => FP, _}

  implicit val whitespace = {
    import NoWhitespace._
    implicit ctx: ParsingRun[_] =>
      NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  type P[T] = FP[T]

  def getLineAndColumn(index: Int): (Int, Int) = {
    // val Array(line, col) = ctx.input.prettyIndex(index).split(":").map(_.toInt) //?
    // (line, col)
    var left = index
    var i = 0
    val arr = FastParser._lines
    while (i < arr.length && left >= arr(i)){
      left -= arr(i)
      i += 1
    }
    val r1 = (i + 1, left + 1)
    r1
  }

  def setPosition(n: Any, start: Int, finish: Int): Unit = {
    {
      val (line, column) = getLineAndColumn(start)
      FastPositions.setStart(n, FilePosition(_file, line, column))
    }
    {
      val (line, column) = getLineAndColumn(finish)
      FastPositions.setFinish(n, FilePosition(_file, line, column))
    }
  }

  def P[T](t: P[T])(implicit name: sourcecode.Name, ctx: P[_]): P[T] = {

    t map {
      case node: T => { //? Change to PNode
        //? if (node.isInstanceOf[PFunction])
        //?   println("Of interest.")
        val (beginLine, beginColumn) = getLineAndColumn(ctx.index) //?
        val (endLine, endColumn) = getLineAndColumn(ctx.index)

        _begin = FilePosition(_file, beginLine, beginColumn)
        _end = FilePosition(_file, endLine, endColumn)

        FastPositions.setStart(node, _begin)
        FastPositions.setFinish(node, _end)

        node
      }
    }
  }

  /* When importing a file from standard library, e.g. `include <inc.vpr>`, the file is expected
   * to be located in `resources/${standard_import_directory}`, e.g. `resources/import/inv.vpr`.
   */
  val standard_import_directory = "import"

  var _lines: Array[Int] = null
  var _file: Path = null

  var _begin: FilePosition = FilePosition(null, 0, 0)
  var _end: FilePosition = FilePosition(null, 0, 0)

  def parse(s: String, f: Path, plugins: Option[SilverPluginManager] = None) = {
    _file = f.toAbsolutePath
    val lines = s.linesWithSeparators
    _lines = lines.map(_.length).toArray

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
                  standardImportStatements.update(localPath, PStandardImport(localPath.toString))
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
      PProgram(Seq(), macros, domains, fields, functions, predicates, methods, extensions, errors)
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
        var line = 0
        var column = 0
        if (pos != null) {
          line = pos.line
          column = pos.column
        }
        ParseError(msg, SourcePosition(_file, line, column))
      case _:Throwable =>
    }
  }

  case class RecParser(file: Path) {

    def parses(s: String) = {
      fastparse.parse(s, entireProgram(_))
    }
  }

  // Actual Parser starts from here
  def identContinues[_: P] = CharIn("0-9", "A-Z", "a-z", "$_")

  def keyword[_: P](check: String) = P(Index ~ check ~~ !identContinues ~ Index)//.map({
    // case (begin, end) => //?
    //   val (beginLine, beginColumn) = getLineAndColumn(begin)
    //   val (endLine, endColumn) = getLineAndColumn(end)

    //   val keywordBegin = FilePosition(_file, beginLine, beginColumn)
    //   val keywordEnd = FilePosition(_file, endLine, endColumn)

    //   _keywordPos += check -> (keywordBegin, keywordEnd)
  //})

  def parens[_: P, T](p: => P[T]) = "(" ~ p ~ ")"

  def angles[_: P, T](p: => P[T]) = "<" ~ p ~ ">"

  def quoted[_: P, T](p: => P[T]) = "\"" ~ p ~ "\""

  def foldPExp[E <: PExp](e: PExp, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) =>
      val result = a(t)
      FastPositions.setStart(result, t.start)
      FastPositions.setFinish(result, t.finish)
      result
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
        case None => throw ParseException(s"Plugin failed: ${plugins.get.errors.map(_.toString).mkString(", ")}", importStmt.start)
      }
    } else {
      imported_source
    }
    val p = RecParser(path).parses(transformed_source)
    p match {
      case fastparse.Parsed.Success(prog, _) => prog
      case fail @ fastparse.Parsed.Failure(_, index, extra) =>
        val msg = fail.trace().longMsg
        val (line, col) = LineCol(index)
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
          source.getLines.toArray
        } catch {
          case e@(_: RuntimeException | _: java.io.IOException) =>
            throw ParseException(s"could not import file ($e)", FastPositions.getStart(importStmt))
        } finally {
          source.close()
        }
      } catch {
        case _: java.lang.NullPointerException =>
          throw ParseException(s"""file <$path> does not exist""", FastPositions.getStart(importStmt))
        case e@(_: RuntimeException | _: java.io.IOException) =>
          throw ParseException(s"could not import file ($e)", FastPositions.getStart(importStmt))
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
      throw ParseException(s"""file "$path" does not exist""", FastPositions.getStart(importStmt))
    }

    _file = path
    val source = scala.io.Source.fromInputStream(Files.newInputStream(path))

    val buffer = try {
      source.getLines.toArray
    } catch {
      case e@(_: RuntimeException | _: java.io.IOException) =>
        throw ParseException(s"""could not import file ($e)""", FastPositions.getStart(importStmt))
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
          s"exists at ${uniqueMacroNames(define.idndef.name)}", define.start)
      } else {
        uniqueMacroNames += ((define.idndef.name, define.start))
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
        case (d: PDefine, c) if c.c.inside => throw ParseException("Macros cannot be defined inside magic wands proof scripts", d.start)
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
          s"${nonUsedParameter.mkString(", ")} ", SourcePosition(_file, define.start.line, define.start.column)))
      }
      else
        Seq()
    }

    var warnings = Seq.empty[ParseWarning]

    warnings = (warnings /: globalMacros)(_ ++ allParametersUsedInBody(_))

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
        case Some(s: PSeqn) => Some(PSeqn(linearizeSeqOfNestedStmt(s)))
        case v => v
      }

      if (body != method.body)
        PMethod(method.idndef, method.formalArgs, method.formalReturns, method.pres, method.posts, body)
      else
        method
    }

    val methods = p.methods.map(method => {
      // Collect local macro definitions
      val localMacros = method.deepCollect { case n: PDefine => n }

      warnings = (warnings /: localMacros)(_ ++ allParametersUsedInBody(_))

      // Remove local macro definitions from method
      val methodWithoutMacros =
        if (localMacros.isEmpty)
          method
        else
          method.transform { case mac: PDefine => PSkip().setPos(mac) }()

      linearizeMethod(doExpandDefines(localMacros ++ globalMacros, methodWithoutMacros, p))
    })

    PProgram(p.imports, p.macros, domains, p.fields, functions, predicates, methods, p.extensions, p.errors ++ warnings)
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
      case None => throw ParseException(s"Macro " + name + " used but not present in scope", FastPositions.getStart(name))
    }

    // Check if a string is a valid macro name
    def isMacro(name: String): Boolean = macros.exists(_.idndef.name == name)

    // The position of every node inside the macro is the position where the macro is "called"
    def adaptPositions(body: PNode, f: FastPositioned): Unit = {
      val adapter = StrategyBuilder.SlimVisitor[PNode] {
        case n => {
          FastPositions.setStart(n, f.start, force = true)
          FastPositions.setFinish(n, f.finish, force = true)
        }
      }
      adapter.execute[PNode](body)
    }

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
      case app: PMethodCall if isMacro(app.method.name) => MacroApp(app.method.name, app.args, app)
      case app: PCall if isMacro(app.func.name) => MacroApp(app.func.name, app.args, app)
      case app: PIdnUse if isMacro(app.name) => MacroApp(app.name, Nil, app)
    }

    def detectCyclicMacros(start: PNode, seen: Set[String]): Unit = {
      start.visit(
        matchOnMacroCall.andThen { case MacroApp(name, _, _) =>
          if (seen.contains(name)) {
            val position =
              macros.find(_.idndef.name == name)
                    .fold[Position](NoPosition)(FastPositions.getStart)

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
          val freshVarDecl = PIdnDef(freshVarName)
          adaptPositions(freshVarDecl, varDecl)
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
        PIdnUse(renamesMap(varUse.name))
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

    // Replace variables in macro body, adapt positions correctly (same line number as macro call)
    def replacerOnBody(body: PNode, paramToArgMap: Map[String, PExp], pos: FastPositioned): PNode = {

      // Duplicate the body of the macro to allow for differing type checks depending on the context
      val oldForce = viper.silver.ast.utility.ViperStrategy.forceRewrite
      viper.silver.ast.utility.ViperStrategy.forceRewrite = true
      val replicatedBody = body.deepCopyAll
      viper.silver.ast.utility.ViperStrategy.forceRewrite = oldForce

      // Rename locally bound variables in macro's body
      val bodyWithRenamedVars = renamer.execute[PNode](replicatedBody)
      adaptPositions(bodyWithRenamedVars, pos)

      // Create context
      val context = new PartialContextC[PNode, ReplaceContext](ReplaceContext(paramToArgMap))

      // Replace macro's call arguments for every occurrence of its respective parameters in the body
      val bodyWithReplacedParams = replacer.execute[PNode](bodyWithRenamedVars, context)
      adaptPositions(bodyWithReplacedParams, pos)

      // Return expanded macro's body
      bodyWithReplacedParams
    }

    def ExpandMacroIfValid(macroCall: PNode, ctx: ContextA[PNode]): PNode = {
      matchOnMacroCall.andThen {
        case MacroApp(name, arguments, call) =>
          val macroDefinition = getMacroByName(name)
          val parameters = macroDefinition.parameters.getOrElse(Nil)
          val body = macroDefinition.body
          val pos = FastPositions.getStart(call)

          if (arguments.length != parameters.length)
            throw ParseException("Number of macro arguments does not match", pos)

          (call, body) match {
            case (_: PStmt, _: PExp) =>
              throw ParseException("Expression macro used in statement position", pos)
            case (_: PExp, _: PStmt) =>
              throw ParseException("Statement macro used in expression position", pos)
            case _ =>
          }

          /* TODO: The current unsupported position detection is probably not exhaustive.
           *       Seems difficult to concisely and precisely match all (il)legal cases, however.
           */
          (ctx.parent, body) match {
            case (PAccPred(loc, _), _) if (loc eq call) && !body.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, pos)
            case (_: PCurPerm, _) if !body.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, pos)
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
            replacerOnBody(body, mapParamsToArgs(parameters, arguments), call)
          } catch {
            case problem: ParseTreeDuplicationError =>
              throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, pos)
          }
      }.applyOrElse(macroCall, (_: PNode) => macroCall)
    }

    // Strategy that checks if the macro calls are valid and expands them.
    // Requires that macro calls are acyclic
    val expander = StrategyBuilder.Ancestor[PNode] {

      // Handles macros on the left hand-side of assignments
      case (PMacroAssign(call, exp), ctx) =>
        if (!isMacro(call.opName))
          throw ParseException("The only calls that can be on the left-hand side of an assignment statement are calls to macros", FastPositions.getStart(call))

        val body = ExpandMacroIfValid(call, ctx)

        // Check if macro's body can be the left-hand side of an assignment and,
        // if that's the case, add it in a corresponding assignment statement
        body match {
          case fa: PFieldAccess =>
            val node = PFieldAssign(fa, exp)
            adaptPositions(node, fa)
            (node, ctx)
          case _ => throw ParseException("The body of this macro is not a suitable left-hand side for an assignment statement", FastPositions.getStart(call))
        }

      // Handles all other calls to macros
      case (node, ctx) => (ExpandMacroIfValid(node, ctx), ctx)

    }.recurseFunc {
      /* Don't recurse into the PIdnUse of nodes that themselves could represent macro
       * applications. Otherwise, the expansion of nested macros will fail due to attempting
       * to construct invalid AST nodes.
       * Recursing into such PIdnUse nodes caused Silver issue #205.
       */
      case PMacroRef(_) => Seq.empty
      case PMethodCall(targets, _, args) => Seq(targets, args)
      case PCall(_, args, typeAnnotated) => Seq(args, typeAnnotated)
    }.repeat

    try {
      expander.execute[T](subtree)
    } catch {
      case problem: ParseTreeDuplicationError =>
        throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, problem.original.start)
    }
  }

  /** The file we are currently parsing (for creating positions later). */
  def file: Path = _file

  lazy val keywords = Set("result",
    // types
    "Int", "Perm", "Bool", "Ref", "Rational",
    // boolean constants
    "true", "false",
    // null
    "null",
    // preamble importing
    "import",
    // declaration keywords
    "method", "function", "predicate", "program", "domain", "axiom", "var", "returns", "field", "define",
    // specifications
    "requires", "ensures", "invariant",
    // statements
    "fold", "unfold", "inhale", "exhale", "new", "assert", "assume", "package", "apply",
    // control flow
    "while", "if", "elseif", "else", "goto", "label",
    // sequences
    "Seq",
    // sets and multisets
    "Set", "Multiset", "union", "intersection", "setminus", "subset",
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
    "unique") | ParserExtension.extendedKeywords


  def atom(implicit ctx : P[_]) : P[PExp] = P(ParserExtension.newExpAtStart(ctx) | integer | booltrue | boolfalse | nul | old
    | result | unExp
    | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
    | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
    | seqLength | explicitSeqNonEmpty | seqRange | fapp | typedFapp | idnuse | ParserExtension.newExpAtEnd(ctx))


  def result[_: P]: P[PResultLit] = P(keyword("result").map { _ => PResultLit() })

  def unExp[_: P]: P[PUnExp] = P((CharIn("\\-\\!").! ~~ !" " ~~ suffixExpr).map { case (a, b) => PUnExp(a, b) })

  def strInteger[_: P]: P[String] = P(CharIn("0-9").rep(1)).!

  def integer[_: P]: P[PIntLit] = strInteger.filter(s => !s.contains(' ')).map { s => PIntLit(BigInt(s)) }

  def booltrue[_: P]: P[PBoolLit] = P(keyword("true")).map(_ => PBoolLit(b = true))

  def boolfalse[_: P]: P[PBoolLit] = P(keyword("false")).map(_ => PBoolLit(b = false))

  def nul[_: P]: P[PNullLit] = P(keyword("null")).map(_ => PNullLit())

  def identifier[_: P]: P[Unit] = P(CharIn("A-Z", "a-z", "$_") ~~ CharIn("0-9", "A-Z", "a-z", "$_").repX)

  def ident[_: P]: P[String] = P(identifier.!).filter(a => !keywords.contains(a)).opaque("invalid identifier (could be a keyword)")

  def idnuse[_: P]: P[PIdnUse] = P(ident).map(id => {
    val i = PIdnUse(id)
    FastPositions.setStart(i, FastPositions.getStart(id))
    FastPositions.setFinish(i, FastPositions.getFinish(id))
    i
  })

  def oldLabel[_: P]: P[PIdnUse] = P(idnuse | LabelledOld.LhsOldLabel.!).map { case idnuse: PIdnUse => idnuse

  case LabelledOld.LhsOldLabel => PIdnUse(LabelledOld.LhsOldLabel)}

  def old[_: P]: P[PExp] = P(StringIn("old") ~ (parens(exp).map(POld) | ("[" ~ oldLabel ~ "]" ~ parens(exp)).map { case (a, b) => PLabelledOld(a, b) }))

  def magicWandExp[_: P]: P[PExp] = P(orExp ~ (keyword("--*").! ~ exp).?).map { case (a, b) => b match {
    case Some(c) =>
      val x = PMagicWandExp(a, c._2)
      FastPositions.setStart(x, FastPositions.getStart(a))
      FastPositions.setFinish(x, FastPositions.getFinish(a))
      x
    case None => a
  }}

  def realMagicWandExp[_: P]: P[PMagicWandExp] = P(orExp ~ "--*".! ~ exp).map { case (a,_,c) => PMagicWandExp(a,c)}

  def implExp[_: P]: P[PExp] = P(magicWandExp ~ (StringIn("==>").! ~ implExp).?).map {
    case (a, b) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)
      case None => a
    }
  }

  def iffExp[_: P]: P[PExp] = P(implExp ~ ("<==>".! ~ iffExp).?).map {
    case (a, b) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)
      case None => a
    }
  }

  def iteExpr[_: P]: P[PExp] = P(iffExp ~ ("?" ~ iteExpr ~ ":" ~ iteExpr).?).map {
    case (a, b) => b match {
      case Some(c) => PCondExp(a, c._1, c._2)
      case None => a
    }
  }

  def exp[_: P]: P[PExp] = P(iteExpr)

  def suffix[_: P]: P[SuffixedExpressionGenerator[PExp]] =
    P(("." ~ idnuse).map { id => SuffixedExpressionGenerator[PExp]((e: PExp) => {
      val x = PFieldAccess(e, id)
      FastPositions.setStart(x, _begin)
      FastPositions.setFinish(x, _end)
      x
    }) } |
      ("[" ~ Pass ~ ".." ~/ exp ~ "]").map { n => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqTake(e, n)) } |
      ("[" ~ exp ~ ".." ~ Pass ~ "]").map { n => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(e, n)) } |
      ("[" ~ exp ~ ".." ~ exp ~ "]").map { case (n, m) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(PSeqTake(e, m), n)) } |
      ("[" ~ exp ~ "]").map { e1 => SuffixedExpressionGenerator[PExp]((e0: PExp) => PSeqIndex(e0, e1)) } |
      ("[" ~ exp ~ ":=" ~ exp ~ "]").map { case (i, v) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqUpdate(e, i, v)) })

  def suffixExpr[_: P]: P[PExp] = P((atom ~ suffix.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  def realSuffixExpr[_: P]: P[PExp] = P((atom ~ suffix.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  def termOp[_: P]: P[String] = P(StringIn("*", "/", "\\", "%").!)

  def term[_: P]: P[PExp] = P((suffixExpr ~ termd.rep).map { case (a, ss) => foldPExp[PExp](a, ss) })

  def termd[_: P]: P[SuffixedExpressionGenerator[PExp]] = P(termOp ~ suffixExpr).map { case (op, id) => SuffixedExpressionGenerator[PExp]((e: PExp) => PBinExp(e, op, id)) }

  def sumOp[_: P]: P[String] = P(StringIn("++", "+", "-").! | keyword("union").! | keyword("intersection").! | keyword("setminus").! | keyword("subset").!)

  def sum[_: P]: P[PExp] = P((term ~ sumd.rep).map { case (a, ss) => foldPExp[PBinExp](a, ss) })

  def sumd[_: P]: P[SuffixedExpressionGenerator[PBinExp]] = P(sumOp ~ term).map { case (op, id) => SuffixedExpressionGenerator[PBinExp]((e: PExp) => PBinExp(e, op, id)) }

  def cmpOp[_: P] = P(StringIn("<=", ">=", "<", ">").! | keyword("in").!)

  def cmpExp[_: P]: P[PExp] = P(sum ~ (cmpOp ~ cmpExp).?).map {
    case (a, b) => b match {
      case Some(c) =>
        val binExp = PBinExp(a, c._1, c._2)
        FastPositions.setStart(binExp, FastPositions.getStart(a))
        FastPositions.setFinish(binExp, FastPositions.getFinish(a))
        binExp
      case None => a
    }
  }

  def eqOp[_: P] = P(StringIn("==", "!=").!)

  def eqExp[_: P]: P[PExp] = P(cmpExp ~ (eqOp ~ eqExp).?).map {
    case (a, b) => b match {
      case Some(c) =>
        val binExp = PBinExp(a, c._1, c._2)
        FastPositions.setStart(binExp, FastPositions.getStart(a))
        FastPositions.setFinish(binExp, FastPositions.getFinish(a))
        binExp
      case None => a
    }
  }

  def andExp[_: P]: P[PExp] = P(eqExp ~ ("&&".! ~ andExp).?).map {
    case (a, b) => b match {
      case Some(c) =>
        val binExp = PBinExp(a, c._1, c._2)
        FastPositions.setStart(binExp, FastPositions.getStart(a))
        FastPositions.setFinish(binExp, FastPositions.getFinish(a))
        binExp
      case None => a
    }
  }

  def orExp[_: P]: P[PExp] = P(andExp ~ ("||".! ~ orExp).?).map {
    case (a, b) => b match {
      case Some(c) => PBinExp(a, c._1, c._2)
      case None => a
    }
  }

  def accessPredImpl[_: P]: P[PAccPred] = P((keyword("acc") ~ "(" ~ locAcc ~ ("," ~ exp).? ~ ")").map {
    case (start, finish, loc, perms) => {
      val m = PAccPred(loc, perms.getOrElse(PFullPerm()))
      setPosition(m, start, finish)
      m
    }
  })

  def accessPred[_: P]: P[PAccPred] = P(accessPredImpl.map(acc => {
    val perm = acc.perm
    if (FastPositions.getStart(perm) == NoPosition) {
      FastPositions.setStart(perm, acc.start)
      FastPositions.setFinish(perm, acc.finish)
    }
    acc
  }))

  def resAcc[_: P]: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  def locAcc[_: P]: P[PLocationAccess] = P(fieldAcc | predAcc)

  def fieldAcc[_: P]: P[PFieldAccess] =
    P(NoCut(realSuffixExpr.filter(isFieldAccess)).map {
      case fa: PFieldAccess => fa
      case other => sys.error(s"Unexpectedly found $other")
    })

  def predAcc[_: P]: P[PLocationAccess] = P(fapp)

  def actualArgList[_: P]: P[Seq[PExp]] = P(exp.rep(sep = ","))

  def inhaleExhale[_: P]: P[PExp] = P("[" ~ exp ~ "," ~ exp ~ "]").map { case (a, b) => {
    val x = PInhaleExhaleExp(a, b)
    FastPositions.setStart(x, FastPositions.getStart(a))
    FastPositions.setFinish(x, FastPositions.getFinish(a))
    x
  } }

  def perm[_: P]: P[PExp] =
    P(keyword("none").map(_ => PNoPerm()) | keyword("wildcard").map(_ => PWildcard()) | keyword("write").map(_ => PFullPerm())
    | keyword("epsilon").map(_ => PEpsilon()) | ("perm" ~ parens(resAcc)).map(PCurPerm))

  def let[_: P]: P[PExp] = P(
    ("let" ~/ idndef ~ "==" ~ "(" ~ exp ~ ")" ~ "in" ~ exp).map { case (id, exp1, exp2) =>
      /* Type unresolvedType is expected to be replaced with the type of exp1
       * after the latter has been resolved
       * */
      val unresolvedType = PUnknown().setPos(id)
      val formalArgDecl = PFormalArgDecl(id, unresolvedType).setPos(id)
      val nestedScope = PLetNestedScope(formalArgDecl, exp2).setPos(exp2)

      val l = PLet(exp1, nestedScope)
      FastPositions.setStart(l, FastPositions.getStart(exp1))
      FastPositions.setFinish(l, FastPositions.getFinish(exp1))
      l
    })

  def idndef[_: P]: P[PIdnDef] = P(ident).map({s =>
    val i = PIdnDef(s)
    FastPositions.setStart(i, _begin)
    FastPositions.setFinish(i, _end)
    i})

  def quant[_: P]: P[PExp] = P((keyword("forall") ~ nonEmptyFormalArgList ~ "::" ~ trigger.rep ~ exp).map { case (start, finish, a, b, c) =>
      val fa = PForall(a, b, c)
      setPosition(fa, start, finish)
      fa
    } |
    (keyword("exists") ~ nonEmptyFormalArgList ~ "::" ~ trigger.rep ~ exp).map { case (start, finish, a, b, c) =>
      val ex = PExists(a, b, c)
      setPosition(ex, start, finish)
      ex
    })

  def nonEmptyFormalArgList[_: P]: P[Seq[PFormalArgDecl]] = P(formalArg.rep(min = 1, sep = ","))

  def formalArg[_: P]: P[PFormalArgDecl] = P(idndef ~ ":" ~ typ).map { case (a, b) => PFormalArgDecl(a, b) }

  def typ[_: P]: P[PType] = P(primitiveTyp | domainTyp | seqType | setType | multisetType)

  def domainTyp[_: P]: P[PDomainType] = P((idnuse ~ "[" ~ typ.rep(sep = ",") ~ "]").map { case (a, b) => PDomainType(a, b) } |
    // domain type without type arguments (might also be a type variable)
    idnuse.map(name => {
      val x = PDomainType(name, Nil)
      FastPositions.setStart(x, FastPositions.getStart(name))
      FastPositions.setFinish(x, FastPositions.getFinish(name))
      x
    }))

  def seqType[_: P]: P[PType] = P(keyword("Seq") ~ "[" ~ typ ~ "]").map{ t => PSeqType(t._3)}

  def setType[_: P]: P[PType] = P(keyword("Set") ~ "[" ~ typ ~ "]").map( t => PSetType(t._3))

  def multisetType[_: P]: P[PType] = P(keyword("Multiset") ~ "[" ~ typ ~ "]").map( t => PMultisetType(t._3))

  def primitiveTyp[_: P]: P[PType] = P(keyword("Rational").map(_ => PPrimitiv("Perm"))
    | (StringIn("Int", "Bool", "Perm", "Ref") ~~ !identContinues).!.map(PPrimitiv))

  def trigger[_: P]: P[PTrigger] = P("{" ~/ exp.rep(sep = ",") ~ "}").map(
    s => {
      val x = PTrigger(s)
      FastPositions.setStart(x, FastPositions.getStart(s))
      FastPositions.setFinish(x, FastPositions.getFinish(s))
      x
    })

  def forperm[_: P]: P[PExp] = P(keyword("forperm") ~ nonEmptyFormalArgList ~ "[" ~ resAcc ~ "]" ~ "::" ~ exp).map {
    case (_, _, args, res, body) => PForPerm(args, res, body)
  }

  def unfolding[_: P]: P[PExp] = P(keyword("unfolding") ~ predicateAccessPred ~ "in" ~ exp).map { case (_, _, a, b) => PUnfolding(a, b) }

  def predicateAccessPred[_: P]: P[PAccPred] = P(accessPred | predAcc.map (
    loc => {
      val perm = PFullPerm()
      FastPositions.setStart(perm, loc.start)
      FastPositions.setFinish(perm, loc.finish)
      val m = PAccPred(loc, perm)
      FastPositions.setStart(m, loc.start)
      FastPositions.setFinish(m, loc.finish)
      m
  }))

  def setTypedEmpty[_: P]: P[PExp] = collectionTypedEmpty("Set", PEmptySet)

  def explicitSetNonEmpty[_: P]: P[PExp] = P("Set" ~ "(" ~/ exp.rep(sep = ",", min = 1) ~ ")").map(PExplicitSet)

  def explicitMultisetNonEmpty[_: P]: P[PExp] = P("Multiset" ~ "(" ~/ exp.rep(min = 1, sep = ",") ~ ")").map(PExplicitMultiset)

  def multiSetTypedEmpty[_: P]: P[PExp] = collectionTypedEmpty("Multiset", PEmptyMultiset)

  def seqTypedEmpty[_: P]: P[PExp] = collectionTypedEmpty("Seq", PEmptySeq)

  def seqLength[_: P]: P[PExp] = P("|" ~ exp ~ "|").map(PSize)

  def explicitSeqNonEmpty[_: P]: P[PExp] = P("Seq" ~ "(" ~/ exp.rep(min = 1, sep = ",") ~ ")").map(PExplicitSeq)

  private def collectionTypedEmpty[_: P](name: String, typeConstructor: PType => PExp): P[PExp] =
    P(`name` ~ ("[" ~/ typ ~ "]").? ~ "(" ~ ")").map(typ => typeConstructor(typ.getOrElse(PTypeVar("#E"))))


  def seqRange[_: P]: P[PExp] = P("[" ~ exp ~ ".." ~ exp ~ ")").map { case (a, b) => PRangeSeq(a, b) }


  def fapp[_: P]: P[PCall] = P(idnuse ~ parens(actualArgList)).map({
    case (func, args) => {
      val m = PCall(func, args, None)
      FastPositions.setStart(m, _begin)
      FastPositions.setFinish(m, _end)
      FastPositions.setStart(func, _begin)
      FastPositions.setFinish(func, _end)
      m
    }
  })

  def typedFapp[_: P]: P[PExp] = P(parens(idnuse ~ parens(actualArgList) ~ ":" ~ typ)).map {
    case (func, args, typeGiven) => PCall(func, args, Some(typeGiven))
  }

  def stmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | macroassign | fieldassign | localassign | fold | unfold | exhale | assertP |
    inhale | assume | ifthnels | whle | varDecl | defineDecl | newstmt | 
    methodCall | goto | lbl | packageWand | applyWand | macroref | block | ParserExtension.newStmtAtEnd(ctx))

  def nodefinestmt(implicit ctx : P[_]) : P[PStmt] = P(ParserExtension.newStmtAtStart(ctx) | fieldassign | localassign | fold | unfold | exhale | assertP |
    inhale | assume | ifthnels | whle | varDecl | newstmt |
    methodCall | goto | lbl | packageWand | applyWand | macroref | block | ParserExtension.newStmtAtEnd(ctx))

  def macroref[_: P]: P[PMacroRef] = P(idnuse).map(a => PMacroRef(a))

  def fieldassign[_: P]: P[PFieldAssign] = P(fieldAcc ~ ":=" ~ exp).map { case (a, b) => PFieldAssign(a, b) }

  def macroassign[_: P]: P[PMacroAssign] = P(NoCut(fapp) ~ ":=" ~ exp).map { case (call, exp) => PMacroAssign(call, exp) }

  def localassign[_: P]: P[PVarAssign] = P(idnuse ~ ":=" ~ exp).map { case (a, b) => PVarAssign(a, b) }

  def fold[_: P]: P[PFold] = P("fold" ~ predicateAccessPred).map(PFold)

  def unfold[_: P]: P[PUnfold] = P("unfold" ~ predicateAccessPred).map(PUnfold)

  def exhale[_: P]: P[PExhale] = P(keyword("exhale") ~/ exp).map( e => {
    val ex = PExhale(e._3)
    setPosition(ex, e._1, e._2)
    ex
  })

  def assertP[_: P]: P[PAssert] = P(keyword("assert") ~/ exp).map(e => {
    val a = PAssert(e._3)
    setPosition(a, e._1, e._2)
    a
  })

  def inhale[_: P]: P[PInhale] = P(keyword("inhale") ~/ exp).map( e => PInhale(e._3))

  def assume[_: P]: P[PAssume] = P(keyword("assume") ~/ exp).map( e => PAssume(e._3))

  def ifthnels[_: P]: P[PIf] = P("if" ~ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PIf(cond, thn, ele)
  }

  /**
    * This parser is wrapped in another parser because otherwise the position
    * in rules like [[block.?]] are not set properly.
    */
  def block[_: P]: P[PSeqn] = P(P("{" ~/ stmts ~ "}").map(PSeqn))

  def stmts[_: P]: P[Seq[PStmt]] = P(stmt ~/ ";".?).rep

  def elsifEls[_: P]: P[PSeqn] = P(elsif | els)

  def elsif[_: P]: P[PSeqn] = P("elseif" ~/ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PSeqn(Seq(PIf(cond, thn, ele)))
  }

  def els[_: P]: P[PSeqn] = (keyword("else") ~/ block).?.map { block => if (block.isDefined) block.get._3 else PSeqn(Nil)}

  def whle[_: P]: P[PWhile] = P(keyword("while") ~/ "(" ~ exp ~ ")" ~ inv.rep ~ block).map {
    case (start, finish, cond, invs, body) =>
      val x = PWhile(cond, invs, body)
      setPosition(x, start, finish)
      x
  }

  def inv(implicit ctx : P[_]) : P[PExp] = P((keyword("invariant") ~ exp ~ ";".?).map(e => e._3) | ParserExtension.invSpecification(ctx))

  def varDecl[_: P]: P[PLocalVarDecl] = P(keyword("var") ~/ idndef ~ ":" ~ typ ~ (":=" ~ exp).?).map { case (_, _, a, b, c) => PLocalVarDecl(a, b, c) }

  def defineDecl[_: P]: P[PDefine] = P(keyword("define") ~/ idndef ~ ("(" ~ idndef.rep(sep = ",") ~ ")").? ~ (exp | "{" ~ (nodefinestmt ~ ";".?).rep ~ "}")).map {
    case (start, finish, a, b, c) => c match {
      case e: PExp =>
        val x = PDefine(a, b, e)
        setPosition(x, start, finish)
        x
      case ss: Seq[PStmt]@unchecked =>
        val x = PDefine(a, b, PSeqn(ss))
        setPosition(x, start, finish)
        x
    }
  }

  def newstmt[_: P]: P[PNewStmt] = starredNewstmt | regularNewstmt

  def regularNewstmt[_: P]: P[PRegularNewStmt] = P(idnuse ~ ":=" ~ "new" ~ "(" ~ idnuse.rep(sep = ",") ~ ")").map { case (a, b) => PRegularNewStmt(a, b) }

  def starredNewstmt[_: P]: P[PStarredNewStmt] = P(idnuse ~ ":=" ~ "new" ~ "(" ~ "*" ~ ")").map(PStarredNewStmt)

  def methodCall[_: P]: P[PMethodCall] = P((idnuse.rep(sep = ",") ~ ":=").? ~ idnuse ~ parens(exp.rep(sep = ","))).map {
    case (None, method, args) => {
      val m = PMethodCall(Nil, method, args)
      FastPositions.setStart(m, _begin)
      FastPositions.setFinish(m, _end)
      m
    }
    case (Some(targets), method, args) => {
      val m = PMethodCall(targets, method, args)
      FastPositions.setStart(m, _begin)
      FastPositions.setFinish(m, _end)
      m
    }
  }

  def goto[_: P]: P[PGoto] = P("goto" ~/ idnuse).map(PGoto)

  def lbl[_: P]: P[PLabel] = P(keyword("label") ~/ idndef ~ (keyword("invariant") ~/ exp).rep).map { case (_, _, name, invs) => PLabel(name, invs.map( e => e._3 )) }

  def packageWand[_: P]: P[PPackageWand] = P(keyword("package") ~/ magicWandExp ~ block.?).map {
    case (start, finish, wand, Some(proofScript)) =>
      val x = PPackageWand(wand, proofScript)
      setPosition(x, start, finish)
      x
    case (start, finish, wand, None) =>
      val x = PPackageWand(wand, PSeqn(Seq()))
      setPosition(x, start, finish)
      x
  }

  def applyWand[_: P]: P[PApplyWand] = P(keyword("apply") ~/ magicWandExp).map( p => {
    val w = PApplyWand(p._3)
    setPosition(w, p._1, p._2)
    w
  })

  def applying[_: P]: P[PExp] = P(keyword("applying") ~/ "(" ~ magicWandExp ~ ")" ~ "in" ~ exp).map { case (_, _, a, b) => PApplying(a, b) }

  def programDecl(implicit ctx : P[_]) : P[PProgram] = P((ParserExtension.newDeclAtStart(ctx) | preambleImport | defineDecl | domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl | ParserExtension.newDeclAtEnd(ctx)).rep).map {
    decls => {
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
      )
    }
  }

  def preambleImport[_: P]: P[PImport] = P(keyword("import") ~/ (
      quoted(relativeFilePath.!).map(filename => PLocalImport(filename)) |
      angles(relativeFilePath.!).map(filename => PStandardImport(filename))
    )
  ).map(e => {
    setPosition(e._3, e._1, e._2)
    e._3
  })

  def relativeFilePath[_: P]: P[String] = P(CharIn("~.").?.! ~~ (CharIn("/").? ~~ CharIn(".", "A-Z", "a-z", "0-9", "_\\- \n\t")).rep(1))

  def domainDecl[_: P]: P[PDomain] = P("domain" ~/ idndef ~ ("[" ~ domainTypeVarDecl.rep(sep = ",") ~ "]").? ~ "{" ~ (domainFunctionDecl | axiomDecl).rep ~
    "}").map {
    case (name, typparams, members) =>
      val funcs = members collect { case m: PDomainFunction1 => m }
      val axioms = members collect { case m: PAxiom1 => m }
      PDomain(
        name,
        typparams.getOrElse(Nil),
        funcs map (f => PDomainFunction(f.idndef, f.formalArgs, f.typ, f.unique)(PIdnUse(name.name)).setPos(f)),
        axioms map (a => PAxiom(a.idndef, a.exp)(PIdnUse(name.name)).setPos(a)))
  }

  def domainTypeVarDecl[_: P]: P[PTypeVarDecl] = P(idndef).map(PTypeVarDecl)

  def domainFunctionDecl[_: P]: P[PDomainFunction1] = P("unique".!.? ~ domainFunctionSignature  ~ ";".?).map {
    case (unique, fdecl) => fdecl match {
      case (name, formalArgs, t) => PDomainFunction1(name, formalArgs, t, unique.isDefined)
    }
  }

  def domainFunctionSignature[_: P] = P("function" ~ idndef ~ "(" ~ anyFormalArgList ~ ")" ~ ":" ~ typ)

  def anyFormalArgList[_: P]: P[Seq[PAnyFormalArgDecl]] = P((formalArg | unnamedFormalArg).rep(sep = ","))

  def unnamedFormalArg[_: P] = P(typ).map(t => PUnnamedFormalArgDecl(t))

  def functionSignature[_: P] = P("function" ~ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ)

  def formalArgList[_: P]: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))

  def axiomDecl[_: P]: P[PAxiom1] = P(keyword("axiom") ~ idndef.? ~ "{" ~ exp ~ "}" ~ ";".?).map { case (_, _, a, b) => PAxiom1(a, b) }

  def fieldDecl[_: P]: P[PField] = P(keyword("field") ~/ idndef ~ ":" ~ typ ~ ";".?).map({
    case (start, finish, a, b) =>
      val x = PField(a, b)
      setPosition(x, start, finish)
      x
  })

  def functionDecl[_: P]: P[PFunction] = P("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map({ case (a, b, c, d, e, f) =>
      val func = PFunction(a, b, c, d, e, f)
      FastPositions.setStart(func, FastPositions.getStart(b))
      FastPositions.setFinish(func, FastPositions.getFinish(b))
      func
  })


  def pre(implicit ctx : P[_]) : P[PExp] = P(("requires" ~/ exp ~ ";".?) | ParserExtension.preSpecification(ctx))

  def post(implicit ctx : P[_]) : P[PExp] = P(("ensures" ~/ exp ~ ";".?) | ParserExtension.postSpecification(ctx))

  def decCl[_: P]: P[Seq[PExp]] = P(exp.rep(sep = ","))

  def predicateDecl[_: P]: P[PPredicate] = P(keyword("predicate") ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("{" ~ exp ~ "}").?).map {
    case (start, finish, a, b, c) =>
      val x = PPredicate(a, b, c)
      setPosition(x, start, finish)
      x
  }

  def methodDecl[_: P]: P[PMethod] = P(methodSignature ~/ pre.rep ~ post.rep ~ block.?).map {
    case (name, args, rets, pres, posts, body) =>
      val m = PMethod(name, args, rets.getOrElse(Nil), pres, posts, body)
      FastPositions.setStart(m, _begin)
      FastPositions.setFinish(m, _end)
      m
  }

  def methodSignature[_: P] = P("method" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("returns" ~ "(" ~ formalArgList ~ ")").?)

  def entireProgram[_: P]: P[PProgram] = P(Start ~ programDecl ~ End)
}
