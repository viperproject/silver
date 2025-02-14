// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2023 ETH Zurich.

package viper.silver.parser

import viper.silver.ast.{FilePosition, Position, SourcePosition}
import viper.silver.ast.utility.rewriter.{ContextA, ParseTreeDuplicationError, PartialContextC, StrategyBuilder}
import viper.silver.verifier.{ParseError, ParseReport, ParseWarning}

import java.util
import scala.collection.mutable

case class MacroException(msg: String, pos: (Position, Position)) extends Exception

object MacroExpander {
  /**
    * Expands the macros of a PProgram
    *
    * @param p PProgram with macros to be expanded
    * @return PProgram with expanded macros
    */
  def expandDefines(p: PProgram): PProgram = {
    val reports = mutable.Buffer.empty[ParseReport]
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
        reports += ParseError(s"another macro named `${define.idndef.name}` already " +
          s"exists at ${uniqueMacroNames(define.idndef.name)}", define.errorPosition)
      } else {
        uniqueMacroNames += define.idndef.name -> define.errorPosition
      }
    }

    // Check if macros names aren't already taken by other identifiers
    for (name <- globalNamesWithoutMacros) {
      if (uniqueMacroNames.contains(name)) {
        reports += ParseError(s"the macro name `$name` has already been used by another identifier", uniqueMacroNames(name))
      }
    }

    // Check if macros are defined in the right place
    case class InsideMagicWandContext(inside: Boolean = false)
    StrategyBuilder.ContextVisitor[PNode, InsideMagicWandContext](
      {
        case (_: PPackageWand, c) => c.updateContext(c.c.copy(true))
        case (d: PDefine, c) if c.c.inside =>
          reports += ParseError("macros cannot be defined inside magic wands proof scripts", d.errorPosition)
          c
        case (_, c) => c
      }, InsideMagicWandContext()).execute(p)

    // Check if all macro parameters are used in the body
    def allParametersUsedInBody(define: PDefine): Option[ParseWarning] = {
      val (replacer, freeVars) = makeReplacer()
      // Execute with empty replacer, thus no variables will be replaced but freeVars will be filled
      replacer.execute(define)
      val parameters = define.parameters.map(_.inner.toSeq).getOrElse(Seq.empty).map(_.idndef.name).toSet
      val nonUsedParameter = parameters -- freeVars

      if (nonUsedParameter.nonEmpty) {
        Some(ParseWarning(s"in macro `${define.idndef.name}`, the following parameters were defined but not used: " +
          s"${nonUsedParameter.mkString(", ")}", define.errorPosition))
      }
      else
        None
    }

    reports ++= globalMacros.flatMap(allParametersUsedInBody)

    def linearizeMethod(method: PMethod): PMethod = {
      def linearizeSeqOfNestedStmt(ss: PGrouped[PSym.Brace, PDelimited[PStmt, Option[PSym.Semi]]]): PGrouped[PSym.Brace, PDelimited[PStmt, Option[PSym.Semi]]] = {
        def linearizeSeqn(s: PSeqn): PSeqn = PSeqn(linearizeSeqOfNestedStmt(s.ss))(s.pos)
        def linearizeIf(i: PIf): PIf = i match {
          case PIf(k, cond, thn, None) => PIf(k, cond, linearizeSeqn(thn), None)(i.pos)
          case PIf(k, cond, thn, Some(ei: PIf)) =>
            PIf(k, cond, linearizeSeqn(thn), Some(linearizeIf(ei)))(i.pos)
          case PIf(k, cond, thn, Some(e@PElse(ek, els))) =>
            PIf(k, cond, linearizeSeqn(thn), Some(PElse(ek, linearizeSeqn(els))(e.pos)))(i.pos)
        }
        var stmts = Seq.empty[(PStmt, Option[PSym.Semi])]
        (ss.inner.toSeq.zip(ss.inner.delimiters)).foreach {
          case (n: PMacroSeqn, _) =>
            val lin = linearizeSeqOfNestedStmt(n.ss)
            stmts = stmts ++ lin.inner.toSeq.zip(lin.inner.delimiters)
          case (n: PSeqn, s) =>
            stmts = stmts :+ (linearizeSeqn(n), s)
          case (n: PIf, s) =>
            stmts = stmts :+ (linearizeIf(n), s)
          case (n@PWhile(k, cond, invs, body), s) =>
            stmts = stmts :+ (PWhile(k, cond, invs, linearizeSeqn(body))(n.pos), s)
          case (n, s) =>
            stmts = stmts :+ (n, s)
        }
        ss.update(PDelimited(stmts)(ss.inner.pos))
      }

      val body = method.body match {
        case Some(PSeqn(ss)) => Some(PSeqn(linearizeSeqOfNestedStmt(ss))(method.pos))
        case v => v
      }

      if (body != method.body) {
        method.copy(body = body)(method.pos)
      } else {
        method
      }
    }

    def doExpandDefinesAll(program: PProgram, reports: mutable.Buffer[ParseReport] = mutable.Buffer.empty): PProgram = {
      val newImported = program.imported.map(doExpandDefinesAll(_))

      val newMembers = try {
        program.members.map {
          case n: PDomain => doExpandDefines(globalMacros, n, p)
          case n: PFunction => doExpandDefines(globalMacros, n, p)
          case n: PPredicate => doExpandDefines(globalMacros, n, p)
          case n: PMethod => {
            // Collect local macro definitions
            val localMacros = n.deepCollect { case n: PDefine => n }

            reports ++= localMacros.flatMap(allParametersUsedInBody)

            // Remove local macro definitions from method
            val methodWithoutMacros =
              if (localMacros.isEmpty) n
              else StrategyBuilder.Slim[PNode]({ case mac: PDefine => PSkip()(mac.pos) }).execute(n)

            linearizeMethod(doExpandDefines(localMacros ++ globalMacros, methodWithoutMacros, p))
          }
          case n => n
        }
      }
      catch {
        case MacroException(msg, pos) =>
          val location = pos match {
            case (start: FilePosition, end: FilePosition) =>
              SourcePosition(start.file, start, end)
            case _ => program.pos match {
              case (start: FilePosition, end: FilePosition) =>
                SourcePosition(start.file, start, end)
              case _ =>
                pos._1
            }
          }
          return PProgram(newImported, program.members)(program.pos, program.localErrors ++ reports :+ ParseError(msg, location), program.offsets, program.rawProgram)
      }
      PProgram(newImported, newMembers)(program.pos, program.localErrors ++ reports, program.offsets, program.rawProgram)
    }

    doExpandDefinesAll(p, reports)
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
    val scopeOfExpandedMacros = new util.IdentityHashMap[PScope, mutable.Set[String]]()
    var currentMacroScope: PScope = null

    def scope: Set[String] = {
      if (scopeOfExpandedMacros.containsKey(currentMacroScope)) {
        scopeAtMacroCall ++ scopeOfExpandedMacros.get(currentMacroScope)
      } else {
        scopeAtMacroCall
      }
    }

    // Handy method to get a macro from its name string
    def getMacroByName(name: PIdnUse): PDefine = getMacro(name) match {
      case Some(mac) => mac
      case None => throw MacroException(s"macro `${name.name}` used but not present in scope", name.pos)
    }

    // Optionally get a macro from its name
    def getMacro(name: PIdnUse): Option[PDefine] = macros.find(_.idndef.name == name.name)
    // Optionally get a macro from its name, any macros matched should not have parameters
    def getMacroPlain(name: PIdnUse): Option[PDefine] = getMacro(name)

    // Skip any macro without parameters since we want to replace just the `PIdnRef` of the call,
    // not the whole `PCall` itself.
    def getMacroArgs(call: PCall): Option[PDefine] =
      if (call.typeAnnotated.isEmpty) getMacro(call.idnref).filter(_.parameters.isDefined) else None

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
    def mapParamsToArgs(params: Option[Seq[PDefineParam]], args: Option[Seq[PExp]]): Map[String, PExp] = {
      params.getOrElse(Nil).map(_.idndef.name).zip(args.getOrElse(Nil)).toMap
    }

    /* Abstraction over several possible `PNode`s that can represent macro applications */
    case class MacroApp(node: PNode, arguments: Option[Seq[PExp]], macroDefinition: PDefine)

    val matchOnMacroCall: PartialFunction[PNode, MacroApp] = {
      // Macro references in statement position (without arguments)
      case assign@PAssign(_, None, idnuse: PIdnUseExp) if getMacroPlain(idnuse).isDefined =>
        MacroApp(assign, None, getMacroPlain(idnuse).get)
      // Macro references in statement position (with arguments)
      case assign@PAssign(_, None, app: PCall) if getMacroArgs(app).isDefined =>
        MacroApp(assign, Some(app.args), getMacroArgs(app).get)

      // Macro references in type position (without arguments)
      case typ@PDomainType(idnuse, None) if getMacroPlain(idnuse).isDefined =>
        MacroApp(typ, None, getMacroPlain(idnuse).get)
      // Macro references in type position (with arguments)
      case app: PMacroType =>
        MacroApp(app, Some(app.use.args), getMacroByName(app.use.idnref))

      // Other macro refs (without arguments)
      case idnuse: PIdnUse if getMacroPlain(idnuse).isDefined =>
        MacroApp(idnuse, None, getMacroPlain(idnuse).get)
      // Other macro refs (with arguments)
      case app: PCall if getMacroArgs(app).isDefined =>
        MacroApp(app, Some(app.args), getMacroArgs(app).get)
    }

    def detectCyclicMacros(start: PNode, seen: Map[String, PDefine]): Unit = {
      start.visit(
        matchOnMacroCall.andThen { case MacroApp(_, _, macroDefinition) =>
          seen.get(macroDefinition.idndef.name) match {
            case None => {
              detectCyclicMacros(macroDefinition.body, seen + (macroDefinition.idndef.name -> macroDefinition))
            }
            case Some(macroDef) =>
              throw MacroException("Recursive macro declaration found: " + macroDef.idndef.name, macroDef.pos)
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
          scopeOfExpandedMacros.get(currentMacroScope) += freshVarName
          renamesMap += varDecl.name -> freshVarName

          // Create a variable with new name to substitute the previous one
          val freshVarDecl = PIdnDef(freshVarName)(varDecl.pos)

          freshVarDecl
        } else {

          // Update scope
          scopeOfExpandedMacros.get(currentMacroScope) += varDecl.name

          // Return the same variable
          varDecl
        }

      // Variable used: update variable's name according to its declaration
      // Macro's parameters are not renamed, since they will be replaced by
      // their respective arguments in the following steps (by replacer)
      case varUse: PIdnUse if renamesMap.contains(varUse.name) =>
        varUse.rename(renamesMap(varUse.name))
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
        case MacroApp(call, arguments, macroDefinition) =>
          val parameters = macroDefinition.parameters.map(_.inner.toSeq)
          val body = macroDefinition.body

          if (arguments.isEmpty && parameters.isDefined) {
            // `arguments.isDefined && parameters.isEmpty` cannot happen, we rule this out in `getMacroArgs`
            val suggestion = macroDefinition.parameters.get.pretty
            throw MacroException(s"macro `${macroDefinition.idndef.name}` is defined with parameters but referenced without, try adding `${suggestion}`", call.pos)
          }
          if (arguments.map(_.length) != parameters.map(_.length))
            throw MacroException("Number of macro arguments does not match", call.pos)

          (call, body) match {
            case (_: PStmt, _: PStmt) | (_: PExp, _: PExp) | (_: PType, _: PType) | (_: PIdnRef[_], _: PIdnUse) =>
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
                case _: PIdnRef[_] => "identifier"
                case _ => "unknown"
              }
              throw MacroException(s"$expandedType macro used in $callType position", call.pos)
          }

          /* TODO: The current unsupported position detection is probably not exhaustive.
           *       Seems difficult to concisely and precisely match all (il)legal cases, however.
           */
          (ctx.parent, body) match {
            case (PAccPred(_, amount), _) if (amount.inner.first eq call) && !body.isInstanceOf[PLocationAccess] =>
              throw MacroException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, call.pos)
            case (_: PCurPerm, _) if !body.isInstanceOf[PLocationAccess] =>
              throw MacroException("Macro expansion would result in invalid code...\n...occurs in position where a location access is required, but the body is of the form:\n" + body.toString, call.pos)
            case _ => /* All good */
          }

          val newNode = try {
            scopeAtMacroCall = NameAnalyser().namesInScope(program, Some(macroCall))
            ctx.parent match {
              case s: PScope => currentMacroScope = s
              case n => currentMacroScope = customGetEnclosingScope(n).get
            }
            if (!scopeOfExpandedMacros.containsKey(currentMacroScope)) {
              scopeOfExpandedMacros.put(currentMacroScope, mutable.Set.empty)
            }

            // Since we're working on a parse AST that is in the process of being rewritten, some nodes don't have
            // their parent node set (or they have it set incorrectly). As a result, n.getEnclosingScope may not
            // work properly. Since we need this functionality, we re-implement it here using information from the
            // context, in particular, the ancestors of the current node.
            def customGetEnclosingScope(target: PNode): Option[PScope] = {
              var foundTarget = false
              for (current <- ctx.ancestorList.reverseIterator) {
                if (foundTarget) {
                  current match {
                    case s: PScope => return Some(s)
                    case _ =>
                  }
                } else {
                  if (current eq target) {
                    foundTarget = true
                  }
                }
              }
              return None
            }

            def allExpandedNamesOfAllSuperScopes(s: PScope): Unit = {
              if (scopeOfExpandedMacros.containsKey(s)) {
                scopeOfExpandedMacros.get(currentMacroScope) ++= scopeOfExpandedMacros.get(s)
              }
              customGetEnclosingScope(s) match {
                case Some(s) => allExpandedNamesOfAllSuperScopes(s)
                case _ =>
              }
            }

            // If scopeOfExpandedMacros contains superscopes of s, these names are also visible in the current scope,
            // and we have to add them to scopeOfExpandedMacros for the current scope.
            allExpandedNamesOfAllSuperScopes(currentMacroScope)

            arguments.foreach(_.foreach(
              StrategyBuilder.SlimVisitor[PNode] {
                case id: PIdnDef => scopeAtMacroCall += id.name
                case _ =>
              }.execute[PNode](_)
            ))
            StrategyBuilder.SlimVisitor[PNode]({
              case id: PIdnDef => scopeAtMacroCall += id.name
              case _ =>
            }).execute(subtree)
            renamesMap.clear()
            replacerOnBody(body, mapParamsToArgs(parameters, arguments), call.pos)
          } catch {
            case problem: ParseTreeDuplicationError =>
              throw MacroException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, call.pos)
          }
          // The body of the macro might be a PIdnUseExp, but the macro call might be a PIdnRef
          val replaced = macroCall match {
            case macroCall: PIdnRef[_] =>
              macroCall.replace(newNode).getOrElse(
                throw MacroException(s"macro expansion cannot substitute expression `${newNode.pretty}` at ${newNode.pos._1} in non-expression position at ${macroCall.pos._1}.", macroCall.pos)
              )
            case _ => newNode
          }
          ExpandMacroIfValid(replaced, ctx)
      }.applyOrElse(macroCall, (_: PNode) => macroCall)
    }

    // Strategy that checks if the macro calls are valid and expands them.
    // Requires that macro calls are acyclic
    val expander = StrategyBuilder.Ancestor[PNode] {

      // Handles macros on the left hand-side of assignments
      case (assign@PAssign(targets, op, rhs), ctx) =>
        val expandedTargets = targets.toSeq map {
          case call: PCall => {
            if (getMacroArgs(call).isEmpty)
              throw MacroException("The only calls that can be on the left-hand side of an assignment statement are calls to macros", call.pos)
            val body = ExpandMacroIfValid(call, ctx)

            // Check if macro's body can be the left-hand side of an assignment and,
            // if that's the case, add it in a corresponding assignment statement
            body match {
              case target: PExp with PAssignTarget => target
              case _ => throw MacroException("The body of this macro is not a suitable left-hand side for an assignment statement", call.pos)
            }
          }
          case target => target
        }
        val expandedLhs = PAssign(targets.update(expandedTargets), op, rhs)(assign.pos)
        (ExpandMacroIfValid(expandedLhs, ctx), ctx)

      // Handles all other calls to macros
      case (node, ctx) => (ExpandMacroIfValid(node, ctx), ctx)

    }.repeat

    try {
      expander.execute[T](subtree)
    } catch {
      case problem: ParseTreeDuplicationError =>
        throw MacroException("Macro expansion would result in invalid code (encountered ParseTreeDuplicationError:)\n" + problem.getMessage, problem.original.pos)
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
      case (b: PBinder, ctx) =>
        (b, ctx.updateContext(ctx.c.copy(boundVars = ctx.c.boundVars ++ b.boundVars.map(_.idndef.name))))
      // Variable use: macro parameters are replaced by their respective argument expressions
      case (varUse: PIdnUseExp, ctx) if !ctx.c.boundVars.contains(varUse.name) =>
        if (ctx.c.paramToArgMap.contains(varUse.name))
          (ctx.c.paramToArgMap(varUse.name).deepCopyAll, ctx.updateContext(ctx.c.copy(paramToArgMap = ctx.c.paramToArgMap.empty)))
        else {
          freeVars += varUse.name
          (varUse, ctx)
        }
      case (varUse: PIdnRef[_], ctx) if !ctx.c.boundVars.contains(varUse.name) =>
        if (ctx.c.paramToArgMap.contains(varUse.name)) {
          val replacement = ctx.c.paramToArgMap(varUse.name).deepCopyAll
          val replaced = varUse.replace(replacement).getOrElse(
            throw MacroException(s"macro expansion cannot substitute expression `${replacement.pretty}` at ${replacement.pos._1} in non-expression position at ${varUse.pos._1}.", replacement.pos)
          )
          (replaced, ctx.updateContext(ctx.c.copy(paramToArgMap = ctx.c.paramToArgMap.empty)))
        } else {
          freeVars += varUse.name
          (varUse, ctx)
        }
      case (label@PLabel(lbl, lName, invs), ctx) if !ctx.c.boundVars.contains(lName.name) =>
        if (ctx.c.paramToArgMap.contains(lName.name)) {
          val replacement = ctx.c.paramToArgMap(lName.name).deepCopyAll
          val replaced = replacement match {
            case r: PIdnUseExp => PIdnDef(r.name)(r.pos)
            case r =>
              throw MacroException(s"macro expansion cannot substitute expression `${replacement.pretty}` at ${replacement.pos._1} in non-expression position at ${lName.pos._1}.", replacement.pos)
          }
          (PLabel(lbl, replaced, invs)(label.pos), ctx.updateContext(ctx.c.copy(paramToArgMap = ctx.c.paramToArgMap.empty)))
        } else {
          freeVars += lName.name
          (label, ctx)
        }
    }, ReplaceContext())
    (replacer, freeVars)
  }
}
