package semper.sil.ast.utility

import semper.sil.ast._

/** Utility methods for expressions. */
object Expressions {
  def isPure(e: Exp): Boolean = e match {
    case _: AccessPredicate => false

    case UnExp(e0) => isPure(e0)
    case InhaleExhaleExp(in, ex) => isPure(in) && isPure(ex)
    case BinExp(e0, e1) => isPure(e0) && isPure(e1)
    case CondExp(cnd, thn, els) => isPure(cnd) && isPure(thn) && isPure(els)
    case Unfolding(_, in) => isPure(in) /* Assuming that the first argument is pure */
    case QuantifiedExp(_, e0) => isPure(e0)

    case _: Literal
         | _: PermExp
         | _: FuncApp
         | _: DomainFuncApp
         | _: LocationAccess
         | _: AbstractLocalVar
         | _: SeqExp
         | _: SetExp
         | _: MultisetExp
    => true
  }
  
  def purify(e: Exp): Exp = e.transform({
      case _: AccessPredicate => TrueLit()()
    })()

  def whenInhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(in, _) => in
  })

  def whenExhaling(e: Exp) = e.transform()(post = {
    case InhaleExhaleExp(_, ex) => ex
  })

  /** In an expression, instantiate a list of variables with given expressions. */
  def instantiateVariables[E <: Exp]
                          (exp: E, variables: Seq[AbstractLocalVar], values: Seq[Exp])
                          : E = {


    val argNames = (variables map (_.name)).zipWithIndex

    def actualArg(formalArg: String): Option[Exp] = {
      argNames.find(x => x._1 == formalArg) map {
        case (_, idx) => values(idx)
      }
    }

    val res = exp.transform {
      case AbstractLocalVar(name) if actualArg(name).isDefined => actualArg(name).get
    }()
    res
  }

  /* See http://stackoverflow.com/a/4982668 for why the implicit is here. */
  def instantiateVariables[E <: Exp]
                          (exp: E, variables: Seq[LocalVarDecl], values: Seq[Exp])
                          (implicit di: DummyImplicit)
                          : E =

    instantiateVariables(exp, variables map (_.localVar), values)

  def subExps(e: Exp) = e.subnodes collect {
    case e: Exp => e
  }

  // note: dependency on program for looking up function preconditions
  def proofObligations(e: Exp): (Program => Seq[Exp]) = ((prog:Program) => {
    e.reduceTree[Seq[Exp]] {
      (n: Node, subConds: Seq[Seq[Exp]]) =>
        val p = n match {
          case n: Positioned => n.pos
          case _ => NoPosition
        }
        // Conditions for the current node.
        val conds = n match {
          case f@FieldAccess(rcv, _) => List(NeCmp(rcv, NullLit()(p))(p), FieldAccessPredicate(f, WildcardPerm()(p))(p))
          case f: FuncApp => prog.findFunction(f.funcname).pres
          case Div(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case Mod(_, q) => List(NeCmp(q, IntLit(0)(p))(p))
          case _ => Nil
        }
        // Only use non-trivial conditions for the subnodes.
        val nonTrivialSubConds = subConds.map {
          m => m.filter {
            _ != TrueLit()()
          }
        }
        // Combine the conditions of the subnodes depending on what node we currently have.
        val finalSubConds = n match {
          case And(left, _) => {
            val Seq(leftConds, rightConds) = nonTrivialSubConds
            reduceAndProofObs(left, leftConds, rightConds, p)
          }
          case Implies(left, _) => {
            val Seq(leftConds, rightConds) = nonTrivialSubConds
            reduceImpliesProofObs(left, leftConds, rightConds, p)
          }
          case Or(left, _) => {
            val Seq(leftConds, rightConds) = nonTrivialSubConds
            reduceOrProofObs(left, leftConds, rightConds, p)
          }
          case CondExp(cond, _, _) => {
            val Seq(condConds, thenConds, elseConds) = nonTrivialSubConds
            reduceCondExpProofObs(cond, condConds, thenConds, elseConds, p)
          }
          case _ => subConds.flatten
        }
        // The condition of the current node has to be at the end because the subtrees have to be well-formed first.
        finalSubConds ++ conds
    }
  })

  /** Calculates the proof obligations for a conditional expression given the proof obligations of the subexpressions. */
  def reduceCondExpProofObs(cond: Exp, condConds: Seq[Exp], thenConds: Seq[Exp], elseConds: Seq[Exp], p: Position): Seq[Exp] = {
    val guardedBodyConds = if (!thenConds.isEmpty || !elseConds.isEmpty) {
      val combinedThenCond = if (!thenConds.isEmpty)
        thenConds reduce {
          (a, b) => And(a, b)(p)
        }
      else TrueLit()(p)
      val combinedElseCond = if (!elseConds.isEmpty)
        elseConds reduce {
          (a, b) => And(a, b)(p)
        }
      else TrueLit()(p)
      List(CondExp(cond, combinedThenCond, combinedElseCond)(p))
    } else Nil
    condConds ++ guardedBodyConds
  }

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceImpliesProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) =
    reduceLazyBinOpProofObs(left, leftConds, rightConds, p)

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceAndProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) = {
    // We want to make the proof obligations as weak as possible, but we cannot use access predicates as guards,
    // so we need to remove them and make the guard weaker. This makes the proof obligations slightly too strong,
    // but it is the best we can do.
    val guard = purify(left)
    reduceLazyBinOpProofObs(guard, leftConds, rightConds, p)
  }

  /** Calculates the proof obligations of an implication given the proof obligations of the subexpressions. */
  def reduceOrProofObs(left: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position) =
    reduceLazyBinOpProofObs(Not(left)(p), leftConds, rightConds, p)

  /** Calculates the proof obligations of a binary expression which has a second half which will only be evaluated
    * if `evalCond` is true given the proof obligations of the subexpressions. */
  def reduceLazyBinOpProofObs(evalCond: Exp, leftConds: Seq[Exp], rightConds: Seq[Exp], p: Position): Seq[Exp] = {
    val guardedRightConds = if (!rightConds.isEmpty) {
      val combinedRightCond = rightConds reduce {
        (a, b) => And(a, b)(p)
      }
      List(Implies(evalCond, combinedRightCond)(p))
    } else Nil
    leftConds ++ guardedRightConds
  }

  /**
   * Generates trigger sets to cover the variables "vs", by searching the
   * expression "toSearch". Returns a list of pairs of lists of trigger sets
   * couple with the extra variables they require to be quantified over
   * (each list of triggers must contain trigger sets which employ exactly
   * the same extra variables).
   */
  def generateTrigger(exp: QuantifiedExp): Seq[(Seq[Trigger], Seq[LocalVarDecl])] = {
    TriggerGeneration.generateTriggers(exp.variables map (_.localVar), exp.exp)
  }

  /**
   * Code related to automatic trigger generation.  The code is largely based on similar
   * code in Chalice written by Alexander J. Summers.
   */
  object TriggerGeneration {

    var id = 0

    // This is used for searching for triggers for quantifiers around the expression "toSearch". The list "vs" gives the variables which need triggering
    // Returns a list of function applications (the framing function) paired with two sets of variables.
    // The first set of variables shows which of the "vs" occur (useful for deciding how to select applications for trigger sets later)
    // The second set of variables indicated the extra boolean variables which were introduced to "hide" problematic logical/comparison operators which may not occur in triggers.
    // e.g., if vs = [x] and toSearch = f(x, y ==> z) thn a singleton list will be returned, containing (f(x,b),{x},{b}).
    def getFunctionAppsContaining(vs: Seq[LocalVar], toSearch: Exp): (Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])]) = {
      var nestedBoundVars: Seq[LocalVar] = Seq() // count all variables bound in nested quantifiers, to avoid considering function applications mentioning these

      // get all nested bound vars
      toSearch visit {
        case qe: QuantifiedExp =>
          nestedBoundVars ++= (qe.variables map (_.localVar))
      }

     // toSearch.reduceTree[Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])]]((t:Node,results:Seq[Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])]]) => results.flatten)
      // get all function applications
      toSearch.reduceTree[Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])]]((t: Node, results: Seq[Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])]]) => t match {
        case t: PossibleTrigger =>
          var extraVars: Seq[LocalVarDecl] = Seq() // collect extra variables generated for this term
        var containsNestedBoundVars = false // flag to rule out this term
        // closure to generate fresh LocalVar to replace problematic expressions which may not occur in triggers
        val freshVar: (Type => Exp) = {
          ty =>
            val newV = LocalVarDecl("fresh__" + id, ty)()
            id += 1
            extraVars +:= newV
            newV.localVar
        }
          // replaces problematic logical/comparison expressions with fresh boolean variables
          val boolExprEliminator: PartialFunction[Node, Node] = {
            case e: ForbiddenInTrigger => freshVar(e.typ)
          }
          var containedVars: Seq[LocalVar] = Seq()
          val processedArgs = t.getArgs map (_.transform(boolExprEliminator)()) // eliminate all boolean expressions forbidden from triggers, and replace with "extraVars"
          // collect all the sought (vs) variables in the function application
          processedArgs map {
            e => e visit {
              case v@LocalVar(s) =>
                if (nestedBoundVars.contains(v)) containsNestedBoundVars = true
                if (vs.contains(v)) containedVars +:= v
            }
          }
          if (!containsNestedBoundVars && !containedVars.isEmpty)
            results.flatten ++ Seq((t.withArgs(processedArgs), containedVars, extraVars))
          else
            results.flatten
        case Old(_) => results.flatten map {case (pt, vars, extras) => (OldTrigger(pt)(pt.pos,pt.info),vars,extras)}
        case _ => results.flatten
      }
      )
    }

    // Precondition : if vars is non-empty then every (f,vs) pair in functs satisfies the property that vars and vs are not disjoint.
    // Finds trigger sets by selecting entries from "functs" until all of "vars" occur, and accumulating the extra variables needed for each function term.
    // Returns a list of the trigger sets found, paired with the extra boolean variables they use
    def buildTriggersCovering(vars: Seq[LocalVar], functs: Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])], currentTrigger: Seq[Exp], extraVars: Seq[LocalVarDecl]): Seq[(Trigger, Seq[LocalVarDecl])] = {
      if (vars.isEmpty) Seq((Trigger(currentTrigger)(), extraVars)) // we have found a suitable trigger set
      else functs match {
        case Nil => Nil // this branch didn't result in a solution
        case ((f, vs, extra) :: rest) => {
          val needed: Seq[LocalVar] = vars.diff(vs) // variables still not triggered
          // try adding the next element of functs, or not..
          buildTriggersCovering(needed, rest.filter(func => !func._2.intersect(needed).isEmpty), currentTrigger :+ f.asExp, (extraVars ++ extra).distinct) ++ buildTriggersCovering(vars, rest, currentTrigger, extraVars)
        }
      }
    }

    // Generates trigger sets to cover the variables "vs", by searching the expression "toSearch".
    // Returns a list of pairs of lists of trigger sets couple with the extra variables they require to be quantified over (each list of triggers must contain trigger sets which employ exactly the same extra variables).
    def generateTriggers(vs: Seq[LocalVar], toSearch: Exp): Seq[(Seq[Trigger], Seq[LocalVarDecl])] = {
      val functionApps: (Seq[(PossibleTrigger, Seq[LocalVar], Seq[LocalVarDecl])]) = getFunctionAppsContaining(vs, toSearch) // find suitable function applications
      if (functionApps.isEmpty) Seq()
      else {
        val candidates: Seq[(Trigger, Seq[LocalVarDecl])] = buildTriggersCovering(vs, functionApps, Nil, Seq())
        
        // filter out any trigger sets with redundant terms (e.g., {g(x),f(g(x))}) - entire set is dropped, since the version without redundancy will also be found (e.g. {f(g(x))})
        val filteredCandidates: Seq[(Trigger, Seq[LocalVarDecl])] = candidates.filter(_._1 match { case Trigger(exps) => (!exps.exists(t1 => exps.exists(t2 => t1.hasSubterm(t2)))) } )

        // now remove any trigger sets which are "subsumed" by another trigger set (in the sense that they define a strictly weaker criterion).
        // The criterion used here is that a set is weaker than another iff every term in the first set is a strict subterm of some term in the second set.
        // Note that it may be that this criterion could be generalised (using some unification to spot e.g. that f(g(x),g(y)) is stricter than f(x,y), but this is not done here.
        var triggerSetsToUse: Seq[(Trigger, Seq[LocalVarDecl])] = filteredCandidates.filter(trig => trig._1 match { case Trigger(exps) => 
          !filteredCandidates.exists(other => other!=trig && (other._1 match { case Trigger(other_exps) => 
            exps.forall(exp => other_exps.exists(_.hasSubterm(exp)))
          })) 
        })
        
        // Finally, group trigger sets by those which use the same sets of extra boolean variables
        var groupedTriggerSets: Seq[(Seq[Trigger], Seq[LocalVarDecl])] = Seq() 
        
        while (!triggerSetsToUse.isEmpty) {
          triggerSetsToUse.partition((ts: (Trigger, Seq[LocalVarDecl])) => triggerSetsToUse.head._2.equals(ts._2)) match {
            case (sameVars, rest) =>
              triggerSetsToUse = rest
              groupedTriggerSets +:=(sameVars map (_._1), sameVars.head._2.toList)
          }
        }
        groupedTriggerSets
      }
    }
    
    def filterTriggers(vs: Seq[LocalVar], triggersToFilter: Seq[(Trigger, Seq[LocalVarDecl])], filteredTriggers: Seq[(Trigger, Seq[LocalVarDecl])]) : Seq[(Trigger, Seq[LocalVarDecl])] =
      
      triggersToFilter match {
        case Nil => filteredTriggers
        case ((triggerSet, extraVars) :: rest) => {
          if(filteredTriggers.exists(_ => true)) filteredTriggers else filteredTriggers
        }
      }
      
    
      
      
  }
}
