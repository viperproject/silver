// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import scala.util.parsing.input.{NoPosition, Position}
import viper.silver.ast._
import viper.silver.ast.utility.rewriter.Traverse
import viper.silver.parser.{FastParser, ParserExtension}
import viper.silver.verifier.ConsistencyError
import viper.silver.{FastMessage, FastMessaging}

/** An utility object for consistency checking. */
object Consistency {
  var messages: FastMessaging.Messages = Nil
  def recordIfNot(suspect: Positioned, property: Boolean, message: String) {
    if (!property) {
      val pos = suspect.pos match {
        case rp: AbstractSourcePosition =>
          new Position {
            val line = rp.line
            val column = rp.column
            val lineContents = "<none>"
          }
        case rp: HasLineColumn =>
          new Position {
            val line = rp.line
            val column = rp.column
            val lineContents = "<none>"
          }
        case rp@viper.silver.ast.NoPosition => NoPosition
      }

      this.messages ++= FastMessaging.aMessage(FastMessage(message,pos))  // this is the way to construct a message directly with a position (only).
    }
  }

  def resetMessages() { this.messages = Nil }
  @inline
  def recordIf(suspect: Positioned, property: Boolean, message: String) =
    recordIfNot(suspect, !property, message)

  /** Names that are not allowed for use in programs. */
  def reservedNames: Seq[String] = _reservedNames
  lazy val _reservedNames = Seq("result",
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
    "unfolding", "in", "applying",
    // old expression
    "old", FastParser.LHS_OLD_LABEL,
    // other expressions
    "let",
    // quantification
    "forall", "exists", "forperm",
    // permission syntax
    "acc", "wildcard", "write", "none", "epsilon", "perm",
    // modifiers
    "unique") ++ ParserExtension.extendedKeywords

  /** Returns true iff the string `name` is a valid identifier. */
  val identFirstLetter = "[a-zA-Z$_]"

  /** Special characters other than dollar ($) and underscore (_) are reserved
    * for Viper-internal use.
    */
  val identOtherLetterChars = "a-zA-Z0-9$_'@"
  val identOtherLetter = s"[$identOtherLetterChars]"
  val identifier = identFirstLetter + identOtherLetter + "*"

  def validIdentifier(name: String) = ("^" + identifier + "$").r.findFirstIn(name).isDefined

  /** Returns true iff the string `name` is a valid identifier, and not a reserved word. */
  def validUserDefinedIdentifier(name: String) = validIdentifier(name) && !reservedNames.contains(name)

  /** Returns true iff the two arguments are of equal length. */
  def sameLength[S, T](a: Seq[T], b: Seq[S]) = a.size == b.size

  /** Returns true iff the first argument can be assigned to the second one,
    * i.e. if the type of the first one is a subtype of the type of the second one. */
  def isAssignable(a: Typed, b: Typed) = a isSubtype b

  /** Returns true iff the arguments are equal of length and
    * the elements of the first argument are assignable to the corresponding elements of the second argument */
  def areAssignable(a: Seq[Typed], b: Seq[Typed]) = sameLength(a, b) && ((a zip b) forall (t => isAssignable(t._1, t._2)))

  /** Returns true iff there are no duplicates. */
  def noDuplicates[T](a: Seq[T]) = a.distinct.size == a.size

  /** Returns true if the given node contains no old expression. */
  def noOld(n: Node) = !n.existsDefined { case _: Old => }

  /** Returns true if the given node contains no labelled-old expression. */
  def noLabelledOld(n: Node) = !n.existsDefined { case LabelledOld(_, label) if label != FastParser.LHS_OLD_LABEL => }

  /** Returns true if the given node contains no result. */
  def noResult(n: Node) = !n.existsDefined { case _: Result => }

  /** Returns true if the given node contains no perm expression.*/
  def noPerm(n: Node)  = !n.existsDefined { case _: CurrentPerm => }

  /** Returns true if the given node contains no forperm expression.*/
  def noForPerm(n: Node)  = !n.existsDefined { case _: ForPerm => }

  /** Returns true if the given node contains no location accesses. */
  def noLocationAccesses(n: Node) = !n.existsDefined { case _: LocationAccess => }

  /** Returns true if the given node contains no accessibility predicates (unfolding predicates is
    * allowed) and no magic wands (applying wands is allowed).
    */
  def noPermissions(n: Node) = {
    /* TODO: The rewriter framework currently doesn't support visitors or collectors,
     *       i.e. strategies that executed for their side-effects or results, but that don't
     *       modify the visited AST.
     */
    var found = false

    val findPermissions = ViperStrategy.Ancestor({
      case (acc: FieldAccessPredicate, _) =>
        found = true
        acc
      case (acc: PredicateAccessPredicate, c) if c.parentOption.fold(true)(!_.isInstanceOf[Unfolding]) =>
        found = true
        acc
      case (mw: MagicWand, c) if c.parentOption.fold(true)(!_.isInstanceOf[Applying]) =>
        found = true
        mw
    }).traverse(Traverse.Innermost)


    findPermissions.execute[Exp](n)
    /*
    An extremely narrow temporary fix by G Rahul Kranti Kiran for using the termination check plugin
     */
    if(n.isInstanceOf[ExtensionExp])
      true
    else
      !found
  }

  /** Convenience methods to treat null values as some other default values (e.g treat null as empty List) */
  def nullValue[T](a: T, b: T) = if (a != null) a else b

  /**
   * Checks that this boolean expression is pure i.e. it contains no magic wands, access predicates or ghost operations.
   */
  def checkPure(e: Exp): Seq[ConsistencyError] = {
    if(!e.isPure){
      Seq(ConsistencyError( s"$e is non pure and appears where only pure expressions are allowed.", e.pos))
    }else{
      Seq()
    }
  }

  /** Checks that no perm or forperm expression occurs in a node, except inside inhale/exhale statements */
  def checkNoPermForpermExceptInhaleExhale(e: Exp) : Seq[ConsistencyError] = {
    val permsAndForperms: Seq[Node] = e.deepCollect({case p: CurrentPerm => p; case fp: ForPerm => fp})
    val inhalesExhales: Seq[Node] = e.deepCollect({case ie: InhaleExhaleExp => ie})
    permsAndForperms.flatMap(p=>{
      inhalesExhales.find(_.contains(p)) match {
        case Some(node) => Seq()
        case None => Seq(ConsistencyError("Perm and forperm in this context are only allowed if nested under inhale-exhale assertions.", p.asInstanceOf[Positioned].pos))
      }
    })
  }

  /** Check all properties required for a function body. */
  def checkFunctionBody(e: Exp) : Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    if(!noOld(e)) s :+= ConsistencyError( "Old expressions are not allowed in functions bodies.", e.pos)
    if(!noResult(e)) s :+= ConsistencyError( "Result expressions are not allowed in functions bodies.", e.pos)
    if(!noForPerm(e)) s :+= ConsistencyError( "Function bodies are not allowed to contain forperm expressions", e.pos)
    if(!noPerm(e)) s :+= ConsistencyError( "Function bodies are not allowed to contain perm expressions", e.pos)
    s ++= checkPure(e)
    s
  }

  /** Checks that none of the given formal arguments are reassigned inside the body. */
  def checkNoArgsReassigned(args: Seq[LocalVarDecl], b: Stmt): Seq[ConsistencyError] = {
    val argVars = args.map(_.localVar).toSet
    var s = Seq.empty[ConsistencyError]

    for (a@LocalVarAssign(l, _) <- b if argVars.contains(l)) {
      s :+= ConsistencyError(s"$a is a reassignment of formal argument $l.", a.pos)
    }
    for (f@Fresh(vars) <- b; v <- vars if argVars.contains(v)) {
      s :+= ConsistencyError(s"$f is a reassignment of formal argument $v.", f.pos)
    }
    for (c@MethodCall(_, _, targets) <- b; t <- targets if argVars.contains(t)) {
      s :+= ConsistencyError(s"$c is a reassignment of formal argument $t.", c.pos)
    }
    for (n@NewStmt(l, _) <- b if argVars.contains(l)){
      s :+= ConsistencyError(s"$n is a reassignment of formal argument $l.", n.pos)
    }
    s
  }
  /** Check all properties required for a precondition. */
  def checkPre(e: Exp): Seq[ConsistencyError] = {
    (if(!(e isSubtype Bool)) Seq(ConsistencyError(s"Precondition $e: ${e.typ} must be boolean.", e.pos)) else Seq()) ++
    (if(!noOld(e)) Seq(ConsistencyError("Old expressions are not allowed in preconditions.", e.pos)) else Seq()) ++
    (if(!noLabelledOld(e)) Seq(ConsistencyError("Labelled-old expressions are not allowed in preconditions.", e.pos)) else Seq()) ++
    (if(!noResult(e)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", e.pos)) else Seq())
  }

  /** Check all properties required for a contract expression that is not a postcondition (precondition, invariant, predicate) */
  def checkNonPostContract(e: Exp) : Seq[ConsistencyError]  = {
    (if(!(e isSubtype Bool)) Seq(ConsistencyError(s"Contract $e: ${e.typ} must be boolean.", e.pos)) else Seq()) ++
    (if(!noResult(e)) Seq(ConsistencyError("Result variables are only allowed in postconditions of functions.", e.pos)) else Seq())
  }

  /** Check all properties required for a postcondition */
  def checkPost(e: Exp) : Seq[ConsistencyError]  = {
    (if(!(e isSubtype Bool)) Seq(ConsistencyError(s"Postcondition $e: ${e.typ} must be boolean.", e.pos)) else Seq()) ++
    (if(!noLabelledOld(e)) Seq(ConsistencyError("Labelled-old expressions are not allowed in postconditions.", e.pos)) else Seq())
  }

  /** checks that all quantified variables appear in all triggers */
  def checkAllVarsMentionedInTriggers(variables: Seq[LocalVarDecl], triggers: Seq[Trigger]) : Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    val varsInTriggers : Seq[Seq[LocalVar]] = triggers map(t=>{
      t.deepCollect({case lv: LocalVar => lv})
    })
    variables.foreach(v=>{
      varsInTriggers.foreach(varList=>{
        varList.find(_.name == v.name) match {
          case Some(tr) =>
          case None => s :+= ConsistencyError(s"Variable ${v.name} is not mentioned in one or more triggers.", v.pos)
        }
      })
    })
    s
  }

  def noGhostOperations(n: Node) = !n.existsDefined {
    case u: Unfolding if !u.isPure =>
    case a: Applying if !a.isPure =>
  }

  /** Returns true iff the given expression is a valid trigger. */
  def validTrigger(e: Exp, program: Program): Boolean = {
    e match {
      case Old(nested) => validTrigger(nested, program) // case corresponds to OldTrigger node
      case wand: MagicWand => wand.subexpressionsToEvaluate(program).forall(e => !e.existsDefined {case _: ForbiddenInTrigger => })
      case _ : PossibleTrigger | _: FieldAccess | _: PredicateAccess => !e.existsDefined { case _: ForbiddenInTrigger => }
      case _ => false
    }
  }

  //check if predicate being accessed has just one parameter of type Ref
  def oneRefParam(p : PredicateAccess) : Boolean = {
    p.args.size == 1 && p.args.head.typ == Ref
  }

  def onlyDirectUse(v: LocalVar, e: Exp): Boolean = e match {
    case l: LocalVar => v != l
    case _ => e.subExps.forall(exp => onlyDirectUse(v, exp))
  }

  def allVariablesUsed(vars: Seq[LocalVarDecl], resArgs: Seq[Exp]): Boolean = {
    vars.forall(v => resArgs.exists(a => a == v.localVar ||
      a.deepCollect[LocalVar]{case vr: LocalVar if vr == v.localVar => vr}.nonEmpty))
  }

  //check all properties that need to be satisfied by the arguments of a forperm expression
  def checkForPermArguments(fp: ForPerm, program: Program): Unit = {

    val resArgs = fp.resource match {
      case fa: FieldAccess => Seq(fa.rcv)
      case pa: PredicateAccess => pa.args
      case w: MagicWand => w.subexpressionsToEvaluate(program)
      case other => sys.error(s"Only field access, predicate access and magic wands can be used in 'forperm'" +
                              s"expressions, but found $other instead")
    }

    recordIfNot(fp, allVariablesUsed(fp.variables, resArgs), "All quantified variables need to be used in a resource")

    for (v <- fp.variables) {
      for (arg <- resArgs) {
        if (!arg.isInstanceOf[LocalVar]) {
          recordIfNot(arg, onlyDirectUse(v.localVar, arg), "Quantified arguments can only be used directly")
        }
      }
    }
  }

  def checkTriggers(t: Trigger, program: Program): Unit = {
    t.exps foreach (e => recordIfNot(t, validTrigger(e, program), s"$t is not a valid Trigger"))
  }

//  def checkNoImpureConditionals(wand: MagicWand, program: Program) = {
//    var expsToVisit = wand.left :: wand.right :: Nil
//    var visitedMembers = List[Member]()
//    var conditionals = List[Exp]()
//    var continue = true
//    var ok = true
//
//    while (ok && expsToVisit.nonEmpty) {
//      var newExpsToVisit = List[Exp]()
//
//      expsToVisit.foreach(_.visit {
//        case c: Implies if !c.isPure => ok = false
//        case c: CondExp if !c.isPure => ok = false
//
//        case e: UnFoldingExp =>
//          val predicate = e.acc.loc.loc(program)
//
//          if (!visitedMembers.contains(predicate)) {
//            newExpsToVisit ::= predicate.body
//            visitedMembers ::= predicate
//          }
//      })
//
//      expsToVisit = newExpsToVisit
//    }
//
//    recordIfNot(wand, ok, s"Conditionals transitively reachable from a magic wand must be pure (see issue 16).")
//  }

  def checkNoFunctionRecursesViaPreconditions(program: Program): Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    Functions.findFunctionCyclesViaPreconditions(program) foreach { case (func, cycleSet) =>
      var msg = s"Function ${func.name} recurses via its precondition"

      if (cycleSet.nonEmpty) {
        msg = s"$msg: the cycle contains the function(s) ${cycleSet.map(_.name).mkString(", ")}"
      }

      s :+= ConsistencyError(msg, func.pos)
    }
    s
  }

  /** Checks consistency that is depends on some context. For example, that some expression
    * Foo(...) must be pure except if it occurs inside Bar(...).
    *
    * @param n The starting node of the consistency check.
    * @param c The initial context (optional).
    */
  def checkContextDependentConsistency(n: Node, c: Context = Context()) : Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    n.visitWithContext(c)(c => {
      case Package(_, proofScript @ Seqn(_, locals)) =>
        s ++= checkMagicWandProofScript(proofScript, locals.map({
          case localVar: LocalVarDecl => localVar
        }))
        c.copy(insideWandStatus = InsideWandStatus.Yes)

      case mw @ MagicWand(lhs, rhs) =>
        s ++= checkWandRelatedOldExpressions(lhs, Context(insideWandStatus = InsideWandStatus.Left))
        s ++= checkWandRelatedOldExpressions(rhs, Context(insideWandStatus = InsideWandStatus.Right))

        if(!noGhostOperations(mw))
          s :+= ConsistencyError("Ghost operations may not occur inside of wands.", mw.pos)

        c.copy(insideWandStatus = InsideWandStatus.Yes)

      case po@LabelledOld(_, FastParser.LHS_OLD_LABEL) if !c.insideWandStatus.isInside =>
        s :+= ConsistencyError("Labelled old expressions with \"lhs\" label may only occur inside wands and their proof scripts.", po.pos)
        c

      case FieldAccessPredicate(_, _) |
           PredicateAccessPredicate(_, _) =>
        c.copy(insideAccessPredicateStatus = true)

      case wp@WildcardPerm() if !c.insideAccessPredicateStatus =>
        s :+= ConsistencyError("\"wildcard\" can only be used in accessibility predicates", wp.pos)
        c
    })
    s
  }

  private def checkMagicWandProofScript(script: Stmt, locals: Seq[LocalVarDecl]): Seq[ConsistencyError] =
    script.shallowCollect({
      case fa: FieldAssign =>
        Some(ConsistencyError("Field assignments are not allowed in magic wand proof scripts.", fa.pos))
      case ne: NewStmt =>
        Some(ConsistencyError("New statements statements are not allowed in magic wand proof scripts.", ne.pos))
      case wh: While =>
        Some(ConsistencyError("While statements are not allowed in magic wand proof scripts.", wh.pos))
      case loc @ LocalVarAssign(LocalVar(varName, _), _) if !locals.exists(_.name == varName) =>
        Some(ConsistencyError("Can only assign to local variables that were declared inside the proof script.", loc.pos))
      case _: Package => None
    }).flatten

  private def checkWandRelatedOldExpressions(n: Node, c: Context): Seq[ConsistencyError] = {
    var s = Seq.empty[ConsistencyError]
    n.visitWithContextManually(c) (c => {
      case MagicWand(lhs, rhs) =>
        s ++= checkWandRelatedOldExpressions(lhs, c.copy(insideWandStatus = InsideWandStatus.Left))
        s ++= checkWandRelatedOldExpressions(rhs, c.copy(insideWandStatus = InsideWandStatus.Right))

      case po @ LabelledOld(_, FastParser.LHS_OLD_LABEL) if !c.insideWandStatus.isRight =>
          s :+= ConsistencyError("Wands may use the old[lhs]-expression on the rhs and in their proof script only.", po.pos)
    })
    s
  }

  class InsideWandStatus protected[InsideWandStatus](val isInside: Boolean, val isLeft: Boolean, val isRight: Boolean) {
    assert(!(isLeft || isRight) || isInside, "Inconsistent status")
  }

  object InsideWandStatus {
    val No = new InsideWandStatus(false, false, false)
    val Yes = new InsideWandStatus(true, false, false)
    val Left = new InsideWandStatus(true, true, false)
    val Right = new InsideWandStatus(true, false, true)
  }

  /** Context for context dependent consistency checking. */
  case class Context(insideWandStatus: InsideWandStatus = InsideWandStatus.No,
                     insideAccessPredicateStatus: Boolean = false)
}
