// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.parser

import viper.silver.ast.{FilePosition, Position, SourcePosition}
import viper.silver.ast.utility.rewriter.{ContextA, PartialContextC, StrategyBuilder}
import viper.silver.parser.Transformer.ParseTreeDuplicationError
import viper.silver.verifier.ParseWarning

import scala.collection.mutable

object MacroExpander {
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
    val uniqueMacroNames = new mutable.HashMap[String, (Position, Position)]()
    for (define <- globalMacros) {
      if (uniqueMacroNames.contains(define.idndef.name)) {
        throw ParseException(s"Another macro named '${define.idndef.name}' already " +
          s"exists at ${uniqueMacroNames(define.idndef.name)}", define.pos)
      } else {
        uniqueMacroNames += ((define.idndef.name, define.pos))
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
        case (d: PDefine, c) if c.c.inside => throw ParseException("Macros cannot be defined inside magic wands proof scripts", d.pos)
        case (_, c) => c
      }, InsideMagicWandContext()).execute(p)

    // Check if all macro parameters are used in the body
    def allParametersUsedInBody(define: PDefine): Seq[ParseWarning] = {
      val (replacer, freeVars) = makeReplacer()
      // Execute with empty replacer, thus no variables will be replaced but freeVars will be filled
      replacer.execute(define)
      val parameters = define.parameters.getOrElse(Seq.empty[PIdnDef]).map(_.name).toSet
      val nonUsedParameter = parameters -- freeVars

      if (nonUsedParameter.nonEmpty) {
        val start = define.pos._1.asInstanceOf[FilePosition]
        val end = define.pos._2.asInstanceOf[FilePosition]
        Seq(ParseWarning(s"In macro ${define.idndef.name}, the following parameters were defined but not used: " +
          s"${nonUsedParameter.mkString(", ")} ", SourcePosition(start.file, start, end)))
      }
      else
        Seq()
    }

    var warnings = Seq.empty[ParseWarning]

    warnings = globalMacros.foldLeft(warnings)(_ ++ allParametersUsedInBody(_))

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
      def linearizeSeqOfNestedStmt(ss: Seq[PStmt]): Seq[PStmt] = {
        var stmts = Seq.empty[PStmt]
        ss.foreach {
          case s: PMacroSeqn => stmts = stmts ++ linearizeSeqOfNestedStmt(s.ss)
          case s@PSeqn(ss) => stmts = stmts :+ PSeqn(linearizeSeqOfNestedStmt(ss))(s.pos)
          case i@PIf(cond, t@PSeqn(thn), e@PSeqn(els)) => stmts = stmts :+ PIf(cond, PSeqn(linearizeSeqOfNestedStmt(thn))(t.pos), PSeqn(linearizeSeqOfNestedStmt(els))(e.pos))(i.pos)
          case w@PWhile(cond, invs, b@PSeqn(body)) => stmts = stmts :+ PWhile(cond, invs, PSeqn(linearizeSeqOfNestedStmt(body))(b.pos))(w.pos)
          case v => stmts = stmts :+ v
        }
        stmts
      }

      val body = method.body match {
        case Some(s: PSeqn) => Some(PSeqn(linearizeSeqOfNestedStmt(s.ss))(method.pos))
        case v => v
      }

      if (body != method.body) {
        PMethod(method.idndef, method.formalArgs, method.formalReturns, method.pres, method.posts, body)(method.pos, method.annotations)
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

    // Handy method to get a macro from its name string
    def getMacroByName(name: PIdnUse): PDefine = macros.find(_.idndef.name == name.name) match {
      case Some(mac) => mac
      case None => throw ParseException(s"Macro " + name.name + " used but not present in scope", name.pos)
    }

    // Check if a string is a valid macro name
    def isMacro(name: Option[PIdnUse]): Boolean = name.map(name => macros.exists(_.idndef.name == name.name)).getOrElse(false)

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
    case class MacroApp(idnuse: PIdnUse, arguments: Seq[PExp], node: PNode)

    val matchOnMacroCall: PartialFunction[PNode, MacroApp] = {
      case assign@PAssign(Seq(), app: PMaybeMacroExp) if isMacro(app.possibleMacro) =>
        MacroApp(app.possibleMacro.get, app.macroArgs, assign)
      case app: PMaybeMacroExp if isMacro(app.possibleMacro) => MacroApp(app.possibleMacro.get, app.macroArgs, app)
      case typ@PDomainType(domain, Seq()) if isMacro(Some(domain)) => MacroApp(domain, Seq(), typ)
      case app: PMacroType => MacroApp(app.use.possibleMacro.get, app.use.macroArgs, app)
    }

    def detectCyclicMacros(start: PNode, seen: Map[String, PDefine]): Unit = {
      start.visit(
        matchOnMacroCall.andThen { case MacroApp(idnuse, _, _) =>
          seen.get(idnuse.name) match {
            case None => {
              val macroDef = getMacroByName(idnuse)
              detectCyclicMacros(macroDef.body, seen + (idnuse.name -> macroDef))
            }
            case Some(macroDef) =>
              throw ParseException("Recursive macro declaration found: " + idnuse.name, macroDef.pos)
          }
        }
      )
    }

    detectCyclicMacros(subtree, Map.empty)

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

    val (replacer, _) = makeReplacer()

    // The position of every node inside the macro is the position where the macro is "called"
    def adaptPositions(body: PNode, pos: (Position, Position)): PNode = {
      val children = body.children.map { child => if (child.isInstanceOf[PNode]) adaptPositions(child.asInstanceOf[PNode], pos) else child}
      body.withChildren(children, Some(pos))
    }

    // Replace variables in macro body, adapt positions correctly (same line number as macro call)
    def replacerOnBody(body: PNode, paramToArgMap: Map[String, PExp], pos: (Position, Position)): PNode = {

      // Duplicate the body of the macro to allow for differing type checks depending on the context
      val replicatedBody = body.deepCopyAll match {
        case s@PSeqn(ss) => PMacroSeqn(ss)(s.pos)
        case b => b
      }

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
        case MacroApp(idnuse, arguments, call) =>
          val macroDefinition = getMacroByName(idnuse)
          val parameters = macroDefinition.parameters.getOrElse(Nil)
          val body = macroDefinition.body

          if (arguments.length != parameters.length)
            throw ParseException("Number of macro arguments does not match", call.pos)

          (call, body) match {
            case (_: PStmt, _: PStmt) | (_: PExp, _: PExp) | (_: PType, _: PType) =>
            case _ =>
              val expandedType = body match {
                case _: PExp => "Expression"
                case _: PStmt => "Statement"
                case _: PType => "Type"
                case _ => "Unknown"
              }
              val callType = call match {
                case _: PExp => "expression"
                case _: PStmt => "statement"
                case _: PType => "type"
                case _ => "unknown"
              }
              throw ParseException(s"$expandedType macro used in $callType position", call.pos)
          }

          /* TODO: The current unsupported position detection is probably not exhaustive.
           *       Seems difficult to concisely and precisely match all (il)legal cases, however.
           */
          (ctx.parent, body) match {
            case (PAccPred(loc, _), _) if (loc eq call) && !body.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, call.pos)
            case (_: PCurPerm, _) if !body.isInstanceOf[PLocationAccess] =>
              throw ParseException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, call.pos)
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
              throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, call.pos)
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
            if (!isMacro(call.possibleMacro))
              throw ParseException("The only calls that can be on the left-hand side of an assignment statement are calls to macros", call.pos)
            val body = ExpandMacroIfValid(call, ctx)

            // Check if macro's body can be the left-hand side of an assignment and,
            // if that's the case, add it in a corresponding assignment statement
            body match {
              case target: PAssignTarget => target
              case _ => throw ParseException("The body of this macro is not a suitable left-hand side for an assignment statement", call.pos)
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
      case PCall(_, args, typeAnnotated) => Seq(args, typeAnnotated)
    }.repeat

    try {
      expander.execute[T](subtree)
    } catch {
      case problem: ParseTreeDuplicationError =>
        throw ParseException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, problem.original.pos)
    }
  }

  case class ReplaceContext(paramToArgMap: Map[String, PExp] = Map.empty,
                            boundVars: Set[String] = Set.empty)

  /** Strategy that replaces macro parameters by their respective arguments.
   * The second returned parameter is a Set which collects unreplaced variables
   * (i.e. free variables). When the strategy is executed with the default context
   * no variables are replaced and only free variables are collected. This ensures
   * that both the "unused-parameter" analysis and the actual replacement use the
   * same strategy.
  */
  def makeReplacer() = {
    val freeVars = mutable.Set.empty[String]
    // Strategy to replace macro's parameters by their respective arguments
    val replacer = StrategyBuilder.Context[PNode, ReplaceContext]({
      // Variable binding: add bound variables to the context so that they don't get replaced
      case (b: PBinder, ctx) => (b, ctx.updateContext(ctx.c.copy(boundVars = ctx.c.boundVars ++ b.boundVars.map(_.idndef.name))))
      // Variable use: macro parameters are replaced by their respective argument expressions
      case (varUse: PIdnUse, ctx) if !ctx.c.boundVars.contains(varUse.name) =>
        if (ctx.c.paramToArgMap.contains(varUse.name))
          (ctx.c.paramToArgMap(varUse.name), ctx.updateContext(ctx.c.copy(paramToArgMap = ctx.c.paramToArgMap.empty)))
        else {
          freeVars += varUse.name
          (varUse, ctx)
        }
    }, ReplaceContext())
    (replacer, freeVars)
  }
}
