/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import java.nio.file.{Files, Path}
import scala.util.parsing.input.{NoPosition, Position}
import fastparse.core.Parsed
import fastparse.all
import viper.silver.ast.{LineCol, SourcePosition}
import viper.silver.FastPositions
import viper.silver.ast.utility.Rewriter.{ContextA, PartialContextC, StrategyBuilder}
import viper.silver.parser.Transformer.ParseTreeDuplicationError
import viper.silver.plugin.SilverPluginManager
import viper.silver.verifier.ParseError
import scala.collection.mutable

case class ParseException(msg: String, pos: scala.util.parsing.input.Position) extends Exception

case class SuffixedExpressionGenerator[E <: PExp](func: PExp => E) extends (PExp => PExp) with FastPositioned {
  override def apply(v1: PExp): E = func(v1)
}

object FastParser extends PosParser[Char, String] {

  var _lines: Array[Int] = null

  def parse(s: String, f: Path, plugins: Option[SilverPluginManager] = None) = {
    _file = f.toAbsolutePath
    val lines = s.linesWithSeparators
    _lines = lines.map(_.length).toArray

    // Strategy to handle imports
    // Idea: Import every import reference and merge imported methods, functions, imports, .. into current program
    //       iterate until no new imports are present.

    def resolveImports(p: PProgram) = {
        val pathsToImport = new mutable.ArrayBuffer[Path]()
        val pathImportStatements = new mutable.HashMap[Path, PImport]()
        pathsToImport.append(f.toAbsolutePath)

        var macros = p.macros
        var domains = p.domains
        var fields = p.fields
        var functions = p.functions
        var methods = p.methods
        var predicates = p.predicates
        var errors = p.errors
        for (ip <- p.imports) {
          val importedPath = f.toAbsolutePath.getParent.resolve(ip.file)
          if (!(pathsToImport.contains(importedPath))) {
            pathsToImport.append(importedPath)
            pathImportStatements.update(importedPath, ip)
          }
        }
        var i = 1
        while (i < pathsToImport.length) {
          val current = pathsToImport(i)
          val newProg = importProgram(current, pathImportStatements.get(current).get, plugins)
          macros ++= newProg.macros
          domains ++= newProg.domains
          fields ++= newProg.fields
          functions ++= newProg.functions
          methods ++= newProg.methods
          predicates ++= newProg.predicates
          errors ++= newProg.errors
          for (ip <- newProg.imports) {
            val importedPath = current.getParent.resolve(ip.file)
            if (!(pathsToImport.contains(importedPath))) {
              pathsToImport.append(importedPath)
              pathImportStatements.update(importedPath, ip)
            }
          }
          i += 1
        }
        PProgram(Seq(), macros, domains, fields, functions, predicates, methods, errors)
    }


    try {
      val rp = RecParser(f).parses(s)
      rp match {
        case Parsed.Success(program@PProgram(_, _, _, _, _, _, _, errors), e) =>
          val importedProgram = resolveImports(program) // Import programs
          val expandedProgram = expandDefines(importedProgram) // Expand macros
          Parsed.Success(expandedProgram, e)
        case _ => rp
      }
    }
    catch {
      case e@ParseException(msg, pos) =>
        var line = 0
        var column = 0
        if (pos != null) {
          line = pos.line
          column = pos.column
        }
        ParseError(msg, SourcePosition(_file, line, column))
    }
  }

  case class RecParser(file: Path) {

    def parses(s: String) = {
      fastparser.parse(s)
    }
  }


  val White = PWrapper {
    import fastparse.all._

    NoTrace((("/*" ~ (AnyChar ~ !StringIn("*/")).rep ~ AnyChar ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }

  import fastparse.noApi._

  import White._

  // Actual Parser starts from here
  def identContinues = CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "$_")

  def keyword(check: String) = check ~~ !identContinues

  def parens[A](p: fastparse.noApi.Parser[A]) = "(" ~ p ~ ")"

  def quoted[A](p: fastparse.noApi.Parser[A]) = "\"" ~ p ~ "\""

  def foldPExp[E <: PExp](e: PExp, es: Seq[SuffixedExpressionGenerator[E]]): E =
    es.foldLeft(e) { (t, a) =>
      val result = a(t)
      FastPositions.setStart(result, t.start)
      FastPositions.setFinish(result, a.finish)
      result
    }.asInstanceOf[E]

  def isFieldAccess(obj: Any) = {
    obj.isInstanceOf[PFieldAccess]
  }

  /**
    * Function that parses a file and converts it into a program
    *
    * @param path Path of the file to be imported
    * @param importStmt Import statement.
    * @return `PProgram` node corresponding to the imported program.
    */
  def importProgram(path: Path, importStmt: PImport, plugins: Option[SilverPluginManager]): PProgram = {
    if (java.nio.file.Files.notExists(path))
      throw ParseException(s"""file "$path" does not exist""", FastPositions.getStart(importStmt))
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
      case fastparse.core.Parsed.Success(prog, _) => prog
      case fail @ fastparse.core.Parsed.Failure(_, index, extra) =>
        val msg = all.ParseError(fail).getMessage()
        val (line, col) = LineCol(extra.input, index)
        throw ParseException(s"Expected $msg", FilePosition(path, line, col))
    }
  }

  def pathFromImport(importStmt: PImport): Path = {
    val fileName = importStmt.file
    val path = file.getParent.resolve(fileName)

    path
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

    val globalNames = globalNamesWithoutMacros ++ p.macros.map(_.idndef.name).toSet

    // Check if all macros names are unique
    var uniqueMacroNames = new mutable.HashMap[String, Position]()
    for (define <- globalMacros) {
      if (uniqueMacroNames.contains(define.idndef.name)) {
        throw ParseException(s"Another macro named '${define.idndef.name}' already " +
          s"exists at ${uniqueMacroNames.get(define.idndef.name).get}", define.start)
      } else {
        uniqueMacroNames += ((define.idndef.name, define.start))
      }
    }

    // Check if macros names aren't already taken by other identifiers
    for (name <- globalNamesWithoutMacros) {
      if (uniqueMacroNames.contains(name)) {
        throw ParseException(s"The macro name '$name' has already been used by another identifier", uniqueMacroNames.get(name).get)
      }
    }

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

    val methods = p.methods.map(method => {
      // Collect all method local macros and expand them in the method
      // Remove the method local macros from the method for convenience
      val localMacros = method.deepCollect { case n: PDefine => n }

      val methodWithoutDefines =
        if (localMacros.isEmpty)
          method
        else
          method.transform { case mac: PDefine => PSkip().setPos(mac) }()

      doExpandDefines(localMacros ++ globalMacros, methodWithoutDefines, p)
    })

    PProgram(p.imports, p.macros, domains, p.fields, functions, predicates, methods, p.errors)
  }


  /**
    * Expand a macro inside a PNode of type T
    *
    * @param macros   All macros that could be invoked inside the code
    * @param toExpand The AST node where we want to expand the macros in
    * @param p        root of the AST where the 'toExpand' node belongs to
    * @tparam T       Type of the PNode
    * @return         PNode with expanded macros of type T
    */
  def doExpandDefines[T <: PNode]
                     (macros: Seq[PDefine], toExpand: T, p: PProgram)
                     : T = {
    // Store the replacements from normal variable to freshly generated variable
    val freshNames = mutable.Map.empty[String, String]
    var scopeAtMacroCall = Set.empty[String]
    val scopeOfExpandedMacros = mutable.Set.empty[String]

    def scope: Set[String] = scopeAtMacroCall ++ scopeOfExpandedMacros

    case class ReplaceContext(formalArgumentSubstitutions: Map[String, PExp] = Map.empty)

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
        n => {
          FastPositions.setStart(n, f.start, force = true)
          FastPositions.setFinish(n, f.finish, force = true)
        }
      }
      adapter.execute[PNode](body)
    }

    def getFreshVar(name: String): String =
      getFreshVarWithSuffix(name, 0)

    // Acquire a fresh variable name for a macro definition
    // Rule: newName = name + $ + x where: x >= 0 and newName does not collide with global name
    def getFreshVarWithSuffix(name: String, counter: Int): String = {
      val newName = s"$name$$$counter"

      if (scope.contains(newName)) {
        /* newName would clash with a name already in scope */

        /* TODO: Seems that the implementation could be optimised rather easily to avoid
         *       the linear search for the next "available" identifier
         */
        getFreshVarWithSuffix(name, counter + 1)
      } else {
        newName
      }
    }

    // Create a map that maps the formal parameters to the actual arguments of a macro call
    def mapParamsToArgs(params: Seq[PIdnDef], args: Seq[PExp]): Map[String, PExp] = {
      params.map(_.name).zip(args).toMap
    }

    /* Abstraction over several possible `PNode`s that can represent macro applications */
    case class MacroApp(name: String, arguments: Seq[PExp], node: PNode)

    val matchOnMacroApplication: PartialFunction[PNode, MacroApp] = {
      case app: PMacroRef => MacroApp(app.idnuse.name, Nil, app)
      case app: PMethodCall if isMacro(app.method.name) => MacroApp(app.method.name, app.args, app)
      case app: PCall if isMacro(app.func.name) => MacroApp(app.func.name, app.args, app)
      case app: PIdnUse if isMacro(app.name) => MacroApp(app.name, Nil, app)
    }

    def detectCyclicMacros(start: PNode, seen: Set[String]): Unit = {
      start.visit(
        matchOnMacroApplication.andThen { case MacroApp(name, _, _) =>
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

    detectCyclicMacros(toExpand, Set.empty)

    // Strategy to rename variables declared in macro's body if their names are already used in
    // the scope where the macro is being expanded, avoiding name clashes (hygienic macro expansion)
    val renamer = StrategyBuilder.Context[PNode, ReplaceContext]({

      // Declared variable: either local or bound
      case (varDecl: PIdnDef, _) =>

        // If variable name is already used in scope
        if (scope.contains(varDecl.name)) {

          // Rename variable
          val freshName = getFreshVar(varDecl.name)
          val freshDecl = PIdnDef(freshName)

          // Update scope
          freshNames += varDecl.name -> freshName
          scopeOfExpandedMacros += freshName

          // Preserve positions
          adaptPositions(freshDecl, varDecl)

          // Return renamed variable
          freshDecl
        } else {

          // Update scope
          scopeOfExpandedMacros += varDecl.name

          // Return same variable
          varDecl
        }

      // Variable use: update variable's name according to its declaration
      // Macro's parameters are not renamed, since they will be replaced by
      // their respective arguments in the following steps
      case (varUse: PIdnUse, ctxt) if freshNames.contains(varUse.name) &&
                                      !ctxt.c.formalArgumentSubstitutions.contains(varUse.name) =>
        PIdnUse(freshNames(varUse.name))

    }, ReplaceContext()).duplicateEverything // Duplicate everything to avoid type checker bug with sharing (#191)

    // Strategy to replace macro's parameters by their respective arguments
    val replacer = StrategyBuilder.Context[PNode, ReplaceContext]({

      // Macro parameter
      case (varUse: PIdnUse, ctxt) if ctxt.c.formalArgumentSubstitutions.contains(varUse.name) =>
        ctxt.c.formalArgumentSubstitutions(varUse.name)

    }, ReplaceContext()).duplicateEverything // Duplicate everything to avoid type checker bug with sharing (#191)

    val replacerContextUpdater: PartialFunction[(PNode, ReplaceContext), ReplaceContext] = {
      case (ident: PIdnUse, c) if c.formalArgumentSubstitutions.contains(ident.name) =>
        /* Matches case "replace formal with actual argument" above: having replaced a formal
         * with an actual argument, no further substitutions should be carried out for the
         * plugged-in actual argument.
         */
        c.copy(formalArgumentSubstitutions = c.formalArgumentSubstitutions.empty)
    }

    // Replace variables in macro body, adapt positions correctly (same line number as macro call)
    def replacerOnBody(body: PNode, p2a: Map[String, PExp], pos: FastPositioned): PNode = {
      /* TODO: It would be best if the context updater function were passed as another argument
       *       to the replacer above. That is already possible, but when the replacer is executed
       *       and an initial context is passed, that initial context's updater function (which
       *       defaults to "never update", if left unspecified) replaces the updater function that
       *       was initially passed to renamer.
       */

      // Create context
      val context = new PartialContextC[PNode, ReplaceContext](ReplaceContext(p2a), replacerContextUpdater)

      // Rename locally bound variables in macro's body
      val renamedVarsMacro = renamer.execute[PNode](body, context)
      adaptPositions(renamedVarsMacro, pos)

      // Replace macro's call arguments for every occurrence of its respective parameters in the body
      val replacedParamsMacro = replacer.execute[PNode](renamedVarsMacro, context)
      adaptPositions(replacedParamsMacro, pos)

      // Return expanded macro's body
      replacedParamsMacro
    }

    def ExpandMacroIfValid(node: PNode, ctxt: ContextA[PNode]): PNode = {
      matchOnMacroApplication.andThen {
        case MacroApp(name, actualArgs, app) =>
          val appliedMacro = getMacroByName(name)
          val formalArgs = appliedMacro.args.getOrElse(Nil)
          val macroBody = appliedMacro.body

          if (actualArgs.length != formalArgs.length)
            throw ParseException("Number of macro arguments does not match", FastPositions.getStart(app))

          (app, macroBody) match {
            case (_: PStmt, _: PExp) =>
              throw ParseException("Expression macro used in statement position", FastPositions.getStart(app))
            case (_: PExp, _: PStmt) =>
              throw ParseException("Statement macro used in expression position", FastPositions.getStart(app))
            case _ => /* All good */
          }

          /* TODO: The current unsupported position detection is probably not exhaustive.
           *       Seems difficult to concisely and precisely match all (il)legal cases, however.
           */
          (ctxt.parent, macroBody) match {
            case (PAccPred(loc, _), _) if (loc eq app) && !macroBody.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + macroBody.toString(), FastPositions.getStart(app))
            case (_: PCurPerm, _) if !macroBody.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + macroBody.toString(), FastPositions.getStart(app))
            case _ => /* All good */
          }

          try {
            scopeAtMacroCall = NameAnalyser().namesInScope(p, node)
            freshNames.clear
            replacerOnBody(macroBody, mapParamsToArgs(formalArgs, actualArgs), app)
          } catch {
            case problem: ParseTreeDuplicationError =>
              throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage(), FastPositions.getStart(app))
          }
      }.applyOrElse(node, (_: PNode) => node)
    }

    // Strategy that checks macro applications for legality and then expands them.
    // Relies on all macros being acyclic!
    val expander = StrategyBuilder.Ancestor[PNode] {

      // Handles macros on the left hand-side of assignments
      case (PMacroAssign(call, exp), ctxt) =>
        if (!isMacro(call.opName))
          throw ParseException("The only calls that can be on the left-hand side of an assignment statement are calls to macros", FastPositions.getStart(call))

        val body = ExpandMacroIfValid(call, ctxt)

        // Check if macro's body can be the left-hand side of an assignment and,
        // if that's the case, add it in a corresponding assignment statement
        body match {
          case fa: PFieldAccess =>
            val node = PFieldAssign(fa, exp)
            adaptPositions(node, fa)
            node
          case _ => throw ParseException("The body of this macro is not a suitable left-hand side of an assignment statement", FastPositions.getStart(call))
        }

      // Handles all other calls to macros
      case (currentNode, ctxt) =>
        ExpandMacroIfValid(currentNode, ctxt)

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
      expander.execute[T](toExpand)
    } catch {
      case problem: ParseTreeDuplicationError =>
        throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage(), problem.original.start)
    }
  }

  /** The file we are currently parsing (for creating positions later). */
  def file: Path = _file


  val LHS_OLD_LABEL = "lhs"

  val keywords = Set("result",
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
    "requires", "ensures", "decreases", "invariant",
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
    "unfolding", "in", "applying",
    // old expression
    "old", LHS_OLD_LABEL,
    // other expressions
    "let",
    // quantification
    "forall", "exists", "forperm",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique")


  lazy val atom: P[PExp] = P(integer | booltrue | boolfalse | nul | old
    | result | unExp
    | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
    | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
    | seqLength | explicitSeqNonEmpty | seqRange | fapp | typedFapp | idnuse)


  lazy val result: P[PResultLit] = P(keyword("result").map { _ => PResultLit() })

  lazy val unExp: P[PUnExp] = P((CharIn("-!").! ~ suffixExpr).map { case (a, b) => PUnExp(a, b) })

  lazy val strInteger: P[String] = P(CharIn('0' to '9').rep(1)).!

  lazy val integer: P[PIntLit] = strInteger.filter(s => !s.contains(' ')).map { s => PIntLit(BigInt(s)) }

  lazy val booltrue: P[PBoolLit] = P(keyword("true")).map(_ => PBoolLit(b = true))

  lazy val boolfalse: P[PBoolLit] = P(keyword("false")).map(_ => PBoolLit(b = false))

  lazy val nul: P[PNullLit] = P(keyword("null")).map(_ => PNullLit())

  lazy val identifier: P[Unit] = P(CharIn('A' to 'Z', 'a' to 'z', "$_") ~~ CharIn('0' to '9', 'A' to 'Z', 'a' to 'z', "$_").repX)

  lazy val ident: P[String] = P(identifier.!).filter { case a => !keywords.contains(a) }.opaque("invalid identifier (could be a keyword)")

  lazy val idnuse: P[PIdnUse] = P(ident).map(PIdnUse)

  lazy val oldLabel: P[PIdnUse] = P(idnuse | LHS_OLD_LABEL.!).map { case idnuse: PIdnUse => idnuse
  case LHS_OLD_LABEL => PIdnUse(LHS_OLD_LABEL)}

  lazy val old: P[PExp] = P(StringIn("old") ~ (parens(exp).map(POld) | ("[" ~ oldLabel ~ "]" ~ parens(exp)).map { case (a, b) => PLabelledOld(a, b) }))

  lazy val magicWandExp: P[PExp] = P(orExp ~ ("--*".! ~ exp).?).map { case (a, b) => b match {
    case Some(c) => PMagicWandExp(a, c._2)
    case None => a
  }}

  lazy val realMagicWandExp: P[PMagicWandExp] = P(orExp ~ "--*".! ~ exp).map { case (a,_,c) => PMagicWandExp(a,c)}

  lazy val implExp: P[PExp] = P(magicWandExp ~ (StringIn("==>").! ~ implExp).?).map { case (a, b) => b match {
    case Some(c) => PBinExp(a, c._1, c._2)
    case None => a
  }
  }
  lazy val iffExp: P[PExp] = P(implExp ~ ("<==>".! ~ iffExp).?).map { case (a, b) => b match {
    case Some(c) => PBinExp(a, c._1, c._2)
    case None => a
  }
  }
  lazy val iteExpr: P[PExp] = P(iffExp ~ ("?" ~ iteExpr ~ ":" ~ iteExpr).?).map { case (a, b) => b match {
    case Some(c) => PCondExp(a, c._1, c._2)
    case None => a
  }
  }
  lazy val exp: P[PExp] = P(iteExpr)

  lazy val suffix: fastparse.noApi.Parser[SuffixedExpressionGenerator[PExp]] =
    P(("." ~ idnuse).map { id => SuffixedExpressionGenerator[PExp]((e: PExp) => PFieldAccess(e, id)) } |
      ("[" ~ Pass ~ ".." ~/ exp ~ "]").map { n => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqTake(e, n)) } |
      ("[" ~ exp ~ ".." ~ Pass ~ "]").map { n => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(e, n)) } |
      ("[" ~ exp ~ ".." ~ exp ~ "]").map { case (n, m) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqDrop(PSeqTake(e, m), n)) } |
      ("[" ~ exp ~ "]").map { e1 => SuffixedExpressionGenerator[PExp]((e0: PExp) => PSeqIndex(e0, e1)) } |
      ("[" ~ exp ~ ":=" ~ exp ~ "]").map { case (i, v) => SuffixedExpressionGenerator[PExp]((e: PExp) => PSeqUpdate(e, i, v)) })

  lazy val suffixExpr: P[PExp] = P((atom ~ suffix.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  lazy val realSuffixExpr: P[PExp] = P((atom ~ suffix.rep).map { case (fac, ss) => foldPExp[PExp](fac, ss) })

  lazy val termOp: P[String] = P(StringIn("*", "/", "\\", "%").!)

  lazy val term: P[PExp] = P((suffixExpr ~ termd.rep).map { case (a, ss) => foldPExp[PExp](a, ss) })

  lazy val termd: P[SuffixedExpressionGenerator[PExp]] = P(termOp ~ suffixExpr).map { case (op, id) => SuffixedExpressionGenerator[PExp]((e: PExp) => PBinExp(e, op, id)) }

  lazy val sumOp: P[String] = P(StringIn("++", "+", "-").! | keyword("union").! | keyword("intersection").! | keyword("setminus").! | keyword("subset").!)

  lazy val sum: P[PExp] = P((term ~ sumd.rep).map { case (a, ss) => foldPExp[PBinExp](a, ss) })

  lazy val sumd: P[SuffixedExpressionGenerator[PBinExp]] = P(sumOp ~ term).map { case (op, id) => SuffixedExpressionGenerator[PBinExp]((e: PExp) => PBinExp(e, op, id)) }

  lazy val cmpOp = P(StringIn("<=", ">=", "<", ">").! | keyword("in").!)

  lazy val cmpExp: P[PExp] = P(sum ~ (cmpOp ~ cmpExp).?).map { case (a, b) => b match {
    case Some(c) => PBinExp(a, c._1, c._2)
    case None => a
  }
  }

  lazy val eqOp = P(StringIn("==", "!=").!)

  lazy val eqExp: P[PExp] = P(cmpExp ~ (eqOp ~ eqExp).?).map { case (a, b) => b match {
    case Some(c) => PBinExp(a, c._1, c._2)
    case None => a
  }
  }
  lazy val andExp: P[PExp] = P(eqExp ~ ("&&".! ~ andExp).?).map { case (a, b) => b match {
    case Some(c) => PBinExp(a, c._1, c._2)
    case None => a
  }
  }
  lazy val orExp: P[PExp] = P(andExp ~ ("||".! ~ orExp).?).map { case (a, b) => b match {
    case Some(c) => PBinExp(a, c._1, c._2)
    case None => a
  }
  }

  lazy val accessPredImpl: P[PAccPred] = P((keyword("acc") ~/ "(" ~ locAcc ~ ("," ~ exp).? ~ ")").map {
    case (loc, perms) => PAccPred(loc, perms.getOrElse(PFullPerm()))
  })

  lazy val accessPred: P[PAccPred] = P(accessPredImpl.map {
    case acc => {
      val perm = acc.perm
      if (FastPositions.getStart(perm) == NoPosition) {
        FastPositions.setStart(perm, acc.start)
        FastPositions.setFinish(perm, acc.finish)
      }
      acc
    }
  })

  lazy val resAcc: P[PResourceAccess] = P(locAcc | realMagicWandExp)

  lazy val locAcc: P[PLocationAccess] = P(fieldAcc | predAcc)

  lazy val fieldAcc: P[PFieldAccess] =
    P(NoCut(realSuffixExpr.filter(isFieldAccess)).map {
      case fa: PFieldAccess => fa
      case other => sys.error(s"Unexpectedly found $other")
    })

  lazy val predAcc: P[PLocationAccess] = P(fapp)

  lazy val actualArgList: P[Seq[PExp]] = P(exp.rep(sep = ","))

  lazy val inhaleExhale: P[PExp] = P("[" ~ exp ~ "," ~ exp ~ "]").map { case (a, b) => PInhaleExhaleExp(a, b) }

  lazy val perm: P[PExp] =
    P(keyword("none").map(_ => PNoPerm()) | keyword("wildcard").map(_ => PWildcard()) | keyword("write").map(_ => PFullPerm())
    | keyword("epsilon").map(_ => PEpsilon()) | ("perm" ~ parens(resAcc)).map(PCurPerm))

  lazy val let: P[PExp] = P(
    ("let" ~/ idndef ~ "==" ~ "(" ~ exp ~ ")" ~ "in" ~ exp).map { case (id, exp1, exp2) =>
      /* Type unresolvedType is expected to be replaced with the type of exp1
       * after the latter has been resolved
       * */
      val unresolvedType = PUnknown().setPos(id)
      val formalArgDecl = PFormalArgDecl(id, unresolvedType).setPos(id)
      val nestedScope = PLetNestedScope(formalArgDecl, exp2).setPos(exp2)

      PLet(exp1, nestedScope)
    })

  lazy val idndef: P[PIdnDef] = P(ident).map(PIdnDef)

  lazy val quant: P[PExp] = P((keyword("forall") ~/ nonEmptyFormalArgList ~ "::" ~/ trigger.rep ~ exp).map { case (a, b, c) => PForall(a, b, c) } |
    (keyword("exists") ~/ nonEmptyFormalArgList ~ "::" ~ exp).map { case (a, b) => PExists(a, b) })

  lazy val nonEmptyFormalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(min = 1, sep = ","))

  lazy val formalArg: P[PFormalArgDecl] = P(idndef ~ ":" ~ typ).map { case (a, b) => PFormalArgDecl(a, b) }

  lazy val typ: P[PType] = P(primitiveTyp | domainTyp | seqType | setType | multisetType)

  lazy val domainTyp: P[PDomainType] = P((idnuse ~ "[" ~ typ.rep(sep = ",") ~ "]").map { case (a, b) => PDomainType(a, b) } |
    idnuse.map {
      // domain type without type arguments (might also be a type variable)
      case name => PDomainType(name, Nil)
    })

  lazy val seqType: P[PType] = P(keyword("Seq") ~/ "[" ~ typ ~ "]").map(PSeqType)

  lazy val setType: P[PType] = P(keyword("Set") ~/ "[" ~ typ ~ "]").map(PSetType)

  lazy val multisetType: P[PType] = P(keyword("Multiset") ~/ "[" ~ typ ~ "]").map(PMultisetType)

  lazy val primitiveTyp: P[PType] = P(keyword("Rational").map { case _ => PPrimitiv("Perm") }
    | (StringIn("Int", "Bool", "Perm", "Ref") ~~ !identContinues).!.map(PPrimitiv))

  lazy val trigger: P[PTrigger] = P("{" ~/ exp.rep(sep = ",") ~ "}").map(s => PTrigger(s))

  lazy val forperm: P[PExp] = P(keyword("forperm") ~ nonEmptyFormalArgList ~ "[" ~ resAcc ~ "]" ~ "::" ~/ exp).map {
    case (args, res, body) => PForPerm(args, res, body)
  }

  lazy val unfolding: P[PExp] = P(keyword("unfolding") ~/ predicateAccessPred ~ "in" ~ exp).map { case (a, b) => PUnfolding(a, b) }

  lazy val predicateAccessPred: P[PAccPred] = P(accessPred | predAcc.map {
    case loc => {
      val perm = PFullPerm()
      FastPositions.setStart(perm, loc.start)
      FastPositions.setFinish(perm, loc.finish)
      PAccPred(loc, perm)
    }
  })

  lazy val setTypedEmpty: P[PExp] = collectionTypedEmpty("Set", PEmptySet)

  lazy val explicitSetNonEmpty: P[PExp] = P("Set" ~ "(" ~/ exp.rep(sep = ",", min = 1) ~ ")").map(PExplicitSet)

  lazy val explicitMultisetNonEmpty: P[PExp] = P("Multiset" ~ "(" ~/ exp.rep(min = 1, sep = ",") ~ ")").map(PExplicitMultiset)

  lazy val multiSetTypedEmpty: P[PExp] = collectionTypedEmpty("Multiset", PEmptyMultiset)

  lazy val seqTypedEmpty: P[PExp] = collectionTypedEmpty("Seq", PEmptySeq)

  lazy val seqLength: P[PExp] = P("|" ~ exp ~ "|").map(PSize)

  lazy val explicitSeqNonEmpty: P[PExp] = P("Seq" ~ "(" ~/ exp.rep(min = 1, sep = ",") ~ ")").map(PExplicitSeq)

  private def collectionTypedEmpty(name: String, typeConstructor: PType => PExp): P[PExp] =
    P(`name` ~ ("[" ~/ typ ~ "]").? ~ "(" ~ ")").map(typ => typeConstructor(typ.getOrElse(PTypeVar("#E"))))


  lazy val seqRange: P[PExp] = P("[" ~ exp ~ ".." ~ exp ~ ")").map { case (a, b) => PRangeSeq(a, b) }


  lazy val fapp: P[PCall] = P(idnuse ~ parens(actualArgList)).map {
    case (func, args) => PCall(func, args, None)
  }

  lazy val typedFapp: P[PExp] = P(parens(idnuse ~ parens(actualArgList) ~ ":" ~ typ)).map {
    case (func, args, typeGiven) => PCall(func, args, Some(typeGiven))
  }

  lazy val stmt: P[PStmt] = P(macroassign | fieldassign | localassign | fold | unfold | exhale | assertP |
    inhale | assume | ifthnels | whle | varDecl | defineDecl | newstmt | fresh | constrainingBlock |
    methodCall | goto | lbl | packageWand | applyWand | macroref | block)

  lazy val nodefinestmt: P[PStmt] = P(fieldassign | localassign | fold | unfold | exhale | assertP |
    inhale | assume | ifthnels | whle | varDecl | newstmt | fresh | constrainingBlock |
    methodCall | goto | lbl | packageWand | applyWand | macroref | block)

  lazy val macroref: P[PMacroRef] = P(idnuse).map { case (a) => PMacroRef(a) }

  lazy val fieldassign: P[PFieldAssign] = P(fieldAcc ~ ":=" ~ exp).map { case (a, b) => PFieldAssign(a, b) }

  lazy val macroassign: P[PMacroAssign] = P(NoCut(fapp) ~ ":=" ~ exp).map { case (call, exp) => PMacroAssign(call, exp) }

  lazy val localassign: P[PVarAssign] = P(idnuse ~ ":=" ~ exp).map { case (a, b) => PVarAssign(a, b) }

  lazy val fold: P[PFold] = P("fold" ~ predicateAccessPred).map(PFold)

  lazy val unfold: P[PUnfold] = P("unfold" ~ predicateAccessPred).map(PUnfold)

  lazy val exhale: P[PExhale] = P(keyword("exhale") ~/ exp).map(PExhale)

  lazy val assertP: P[PAssert] = P(keyword("assert") ~/ exp).map(PAssert)

  lazy val inhale: P[PInhale] = P(keyword("inhale") ~/ exp).map(PInhale)

  lazy val assume: P[PAssume] = P(keyword("assume") ~/ exp).map(PAssume)

  lazy val ifthnels: P[PIf] = P("if" ~ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PIf(cond, thn, ele)
  }

  /**
    * This parser is wrapped in another parser because otherwise the position
    * in rules like [[block.?]] are not set properly.
    */
  lazy val block: P[PSeqn] = P(P("{" ~/ stmts ~ "}").map(PSeqn))

  lazy val stmts: P[Seq[PStmt]] = P(stmt ~/ ";".?).rep

  lazy val elsifEls: P[PSeqn] = P(elsif | els)

  lazy val elsif: P[PSeqn] = P("elseif" ~/ "(" ~ exp ~ ")" ~ block ~ elsifEls).map {
    case (cond, thn, ele) => PSeqn(Seq(PIf(cond, thn, ele)))
  }

  lazy val els: P[PSeqn] = (keyword("else") ~/ block).?.map { block => block.getOrElse(PSeqn(Nil)) }

  lazy val whle: P[PWhile] = P(keyword("while") ~/ "(" ~ exp ~ ")" ~ inv.rep ~ block).map {
    case (cond, invs, body) => PWhile(cond, invs, body)
  }

  lazy val inv: P[PExp] = P(keyword("invariant") ~ exp ~ ";".?)

  lazy val varDecl: P[PLocalVarDecl] = P(keyword("var") ~/ idndef ~ ":" ~ typ ~ (":=" ~ exp).?).map { case (a, b, c) => PLocalVarDecl(a, b, c) }

  lazy val defineDecl: P[PDefine] = P(keyword("define") ~/ idndef ~ ("(" ~ idndef.rep(sep = ",") ~ ")").? ~ (exp | "{" ~ (nodefinestmt ~ ";".?).rep ~ "}")).map {
    case (a, b, c) => c match {
      case e: PExp => PDefine(a, b, e)
      case ss: Seq[PStmt]@unchecked => PDefine(a, b, PSeqn(ss))
    }
  }

  lazy val newstmt: P[PNewStmt] = starredNewstmt | regularNewstmt

  lazy val regularNewstmt: P[PRegularNewStmt] = P(idnuse ~ ":=" ~ "new" ~ "(" ~ idnuse.rep(sep = ",") ~ ")").map { case (a, b) => PRegularNewStmt(a, b) }

  lazy val starredNewstmt: P[PStarredNewStmt] = P(idnuse ~ ":=" ~ "new" ~ "(" ~ "*" ~ ")").map(PStarredNewStmt)

  lazy val fresh: P[PFresh] = P(keyword("fresh") ~ idnuse.rep(sep = ",")).map { case vars => PFresh(vars) }

  lazy val constrainingBlock: P[PConstraining] = P("constraining" ~ "(" ~ idnuse.rep(sep = ",") ~ ")" ~ block).map { case (vars, s) => PConstraining(vars, s) }

  lazy val methodCall: P[PMethodCall] = P((idnuse.rep(sep = ",") ~ ":=").? ~ idnuse ~ parens(exp.rep(sep = ","))).map {
    case (None, method, args) => PMethodCall(Nil, method, args)
    case (Some(targets), method, args) => PMethodCall(targets, method, args)
  }

  lazy val goto: P[PGoto] = P("goto" ~/ idnuse).map(PGoto)

  lazy val lbl: P[PLabel] = P(keyword("label") ~/ idndef ~ (keyword("invariant") ~/ exp).rep).map { case (name, invs) => PLabel(name, invs) }

  lazy val packageWand: P[PPackageWand] = P("package" ~/ magicWandExp ~ block.?).map {
    case (wand, Some(proofScript)) => PPackageWand(wand, proofScript)
    case (wand, None) => PPackageWand(wand, PSeqn(Seq()))
  }

  lazy val applyWand: P[PApplyWand] = P("apply" ~/ magicWandExp).map(PApplyWand)

  lazy val applying: P[PExp] = P(keyword("applying") ~/ "(" ~ magicWandExp ~ ")" ~ "in" ~ exp).map { case (a, b) => PApplying(a, b) }

  lazy val programDecl: P[PProgram] = P((preambleImport | defineDecl | domainDecl | fieldDecl | functionDecl | predicateDecl | methodDecl).rep).map {
    decls => {
      PProgram(
        decls.collect { case i: PImport => i }, // Imports
        decls.collect { case d: PDefine => d }, // Macros
        decls.collect { case d: PDomain => d }, // Domains
        decls.collect { case f: PField => f }, // Fields
        decls.collect { case f: PFunction => f }, // Functions
        decls.collect { case p: PPredicate => p }, // Predicates
        decls.collect { case m: PMethod => m }, // Methods
        Seq() // Parse Errors
      )
    }
  }

  lazy val preambleImport: P[PImport] = P(keyword("import") ~/ quoted(relativeFilePath.!)).map {
    case filename => PImport(filename)
  }

  lazy val relativeFilePath: P[String] = P((CharIn("~.").?).! ~~ (CharIn("/").? ~~ CharIn(".", 'A' to 'Z', 'a' to 'z', '0' to '9', "_- \n\t")).rep(1))

  lazy val domainDecl: P[PDomain] = P("domain" ~/ idndef ~ ("[" ~ domainTypeVarDecl.rep(sep = ",") ~ "]").? ~ "{" ~ (domainFunctionDecl | axiomDecl).rep ~
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

  lazy val domainTypeVarDecl: P[PTypeVarDecl] = P(idndef).map(PTypeVarDecl)

  lazy val domainFunctionDecl: P[PDomainFunction1] = P("unique".!.? ~ functionSignature ~ ";".?).map {
    case (unique, fdecl) => fdecl match {
      case (name, formalArgs, t) => PDomainFunction1(name, formalArgs, t, unique.isDefined)
    }
  }

  lazy val functionSignature = P("function" ~ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ)

  lazy val formalArgList: P[Seq[PFormalArgDecl]] = P(formalArg.rep(sep = ","))

  lazy val axiomDecl: P[PAxiom1] = P(keyword("axiom") ~ idndef ~ "{" ~ exp ~ "}" ~ ";".?).map { case (a, b) => PAxiom1(a, b) }

  lazy val fieldDecl: P[PField] = P("field" ~/ idndef ~ ":" ~ typ ~ ";".?).map { case (a, b) => PField(a, b) }

  lazy val functionDecl: P[PFunction] = P("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ dec.? ~ ("{" ~ exp ~ "}").?).map { case (a, b, c, d, e, f, g) => PFunction(a, b, c, d, e, f, g) }


  lazy val pre: P[PExp] = P("requires" ~/ exp ~ ";".?)

  lazy val post: P[PExp] = P("ensures" ~/ exp ~ ";".?)

  lazy val dec: P[PDecClause] = P("decreases" ~/ (("*").!.map{_ => PDecStar()} | (exp.rep(sep = ",").map { exps => PDecTuple(exps)})) ~ ";".?)

  lazy val decCl: P[Seq[PExp]] = P(exp.rep(sep = ","))

  lazy val predicateDecl: P[PPredicate] = P("predicate" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("{" ~ exp ~ "}").?).map { case (a, b, c) => PPredicate(a, b, c) }

  lazy val methodDecl: P[PMethod] = P(methodSignature ~/ pre.rep ~ post.rep ~ block.?).map {
    case (name, args, rets, pres, posts, body) =>
      PMethod(name, args, rets.getOrElse(Nil), pres, posts, body)
  }

  lazy val methodSignature = P("method" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ("returns" ~ "(" ~ formalArgList ~ ")").?)

  lazy val fastparser: P[PProgram] = P(Start ~ programDecl ~ End)


}
