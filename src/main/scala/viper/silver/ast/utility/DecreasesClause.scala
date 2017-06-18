/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.verifier.errors.{AssertFailed, TerminationFailed}
import viper.silver.verifier.reasons.{AssertionFalse, TerminationMeasure, TerminationNoBound}

import scala.collection.mutable

/** Utility methods for DecreaseClauses. */
object DecreasesClause {

  //Delete decClause
  def rewriteForAll(funcs: Seq[Function]): Seq[Function] = {

    var functions = funcs map (deleteDec(_))
    functions
  }

  private def deleteDec(f: Function) = f match {
    case Function(_, _, _, _, _, decs, _) =>
      //f.decs = decs map dec
      f
  }

  //TODO
  // decreases x+y
  // multiple function calls -> multiple assertions
  def addMethod(funcs: Seq[Function], members: mutable.HashMap[String, Node]): Seq[Method] = {
    val decreasingFunc = members.get("decreasing").get.asInstanceOf[DomainFunc]
    val boundedFunc = members.get("bounded").get.asInstanceOf[DomainFunc]
    val methods = funcs map (addTerminationProof(_, decreasingFunc, boundedFunc))
    methods
  }

  private def addTerminationProof(func: Function, decreasingFunc: DomainFunc, boundedFunc:DomainFunc): Method = {
    println("DecClauses: ")
    println(func.decs)
    var m = Method(func.name + "_termination_proof", func.formalArgs, Seq(), func.pres, func.posts, Seq(), Statements.EmptyStmt)(NoPosition, func.info, func.errT)
    m.body = stmt(func.body.get, decreasingFunc, boundedFunc, func)
    m
  }

  def stmt(body: Exp, decreasingFunc: DomainFunc, boundedFunc: DomainFunc, func: Function): Stmt = {

    //TODO replace

    body match {
      case _: AccessPredicate => Statements.EmptyStmt
      case InhaleExhaleExp(in, ex) => Statements.EmptyStmt
      case _: PermExp => Statements.EmptyStmt
      case _: LocationAccess => Statements.EmptyStmt
      case CondExp(cond, thn, els) => If(cond, stmt(thn, decreasingFunc, boundedFunc, func), stmt(els, decreasingFunc, boundedFunc, func))(body.pos)
      case Unfolding(acc, body) =>
        val s1 = Unfold(acc)(body.pos)
        val s2 = stmt(body, decreasingFunc, boundedFunc, func)
        val s3 = Fold(acc)(body.pos)
        val seq = Seq(s1, s2, s3)
        Seqn(seq)(body.pos)
      case _: GhostOperation => Statements.EmptyStmt
      case Let(variable, exp, body) => Statements.EmptyStmt
      case _: QuantifiedExp => Statements.EmptyStmt
      case ForPerm(variable, accessList, body) => Statements.EmptyStmt
      case _: AbstractLocalVar => Statements.EmptyStmt
      case _: SeqExp => Statements.EmptyStmt
      case _: SetExp => Statements.EmptyStmt
      case _: MultisetExp => Statements.EmptyStmt
      case _: Literal => Statements.EmptyStmt
      //case tr: PossibleTrigger =>

      //------------------------------
      //Other Triggers?
      case callee: FuncApp =>

        //TODO
        //check if calledFunc is itself
        //yes do checks
        //no look for itself name: look rec and store already discovered
        //adjust args and give further
        //if found give arg back with conditions

        //method searchFunctionCall(FuncName : String, args) : //maybe not all args
        // (new arg, conditions) //errors?

        val decClause = func.decs

        //Assume only one decreasesClause
        //TODO multiples decreasesClauses
        if (decClause.size >= 0) { //There is a decrease Clause

          //var decreasExpr = decClause

          val paramTypesDecr = decreasingFunc.formalArgs map (_.typ)
          val argTypeVarsDecr = paramTypesDecr.flatMap(p => p.typeVariables)

          //val argTypes = (callee.getArgs map (_.typ))
          //val map = (argTypeVars zip argTypes).toMap

          //var mapDecr = Map(argTypeVarsDecr.head -> decClause.head.typ)

          val callerArgs = func.formalArgs
          val calleeArgs = callee.getArgs

          //Search for VarNames in the decreasing Clausure
          val decreasingVarName = decClause map (_.deepCollect {
            case a: AbstractLocalVar => a
          }.toSet)//TODO toSet? but remain ordering


          //Search the arguments in the called Function, which then sould be repwritten

//          val names = decreasingVarName map (s => s map (_.name))
//          val indexOfDecVar = names map (s => (callerArgs.filter(v => s.contains(v.name))map (callerArgs.indexOf(_))))
//          val usedCalleeArgs = indexOfDecVar map (s => calleeArgs.filter(e => s.contains(calleeArgs.indexOf(e))))

          //TODO put this before and then fix the umweg over _.name
          val callerArgsAsAbstract = callerArgs map (arg => arg match{
            case l: LocalVarDecl => LocalVar(l.name)(l.typ)//, l.pos, l.info, l.errT)
            case a => a
          })

          val smallerExpression = decClause map (_.replace((callerArgsAsAbstract zip calleeArgs).toMap))
          val biggerExpression = decClause map (addOldIfNecessary(_))

          val pos = body.pos
          val infoBound = SimpleInfo(Seq("BoundedCheck"))
          val infoDecr = SimpleInfo(Seq("DecreasingCheck"))

          val errTBound = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
            case k: AssertionFalse => TerminationNoBound(decClause.head, decClause)  //TODO head is not correct
            case k => k
          })
          })

          val errTDecr = ErrTrafo({ case AssertFailed(_, r) => TerminationFailed(callee, r match {
            case k: AssertionFalse => TerminationMeasure(decClause.head, decClause) //TODO head is not correct
            case k => k
          })
          })


          val e = smallerExpression zip biggerExpression

          var decrFunc = Seq.empty[Exp]
          var boundFunc = Seq.empty[Exp]

          for( i <- e.indices){
            if(i>0){
              decrFunc :+= EqCmp(e(i-1)._1,e(i-1)._2)(decreasingFunc.pos)
            }
            decrFunc :+= DomainFuncApp(decreasingFunc, Seq(e(i)._1, e(i)._2), Map(argTypeVarsDecr.head -> e(i)._2.typ))(decreasingFunc.pos)
            boundFunc :+= DomainFuncApp(boundedFunc, Seq(e(i)._1), Map(argTypeVarsDecr.head -> e(i)._1.typ))(boundedFunc.pos)
          }

          val boundedAss = Assert(buildBoundTree(boundFunc))(pos, infoBound, errTBound)
          val decreaseAss = Assert(buildDecTree(decrFunc, true))(pos, infoDecr, errTDecr) //TODO mapDecr

          Seqn(Seq(boundedAss, decreaseAss))(pos) //TODO Position?
        } else { //No DecClause
          println("TODO") //TODO should not be called at all / dont create additional method
          Statements.EmptyStmt
        }

      case b: BinExp => Seqn(Seq(stmt(b.left, decreasingFunc, boundedFunc, func), stmt(b.right, decreasingFunc, boundedFunc, func)))(body.pos)
      case u: UnExp => stmt(u.exp, decreasingFunc, boundedFunc, func)
      case _: Lhs => Statements.EmptyStmt
      case k: ForbiddenInTrigger => k match {
        case CondExp(cond, thn, els) => Statements.EmptyStmt
        case _: DomainOpExp => Statements.EmptyStmt
      }
      case f: FuncLikeApp => f match {
        case FuncApp(funcname, args) => Statements.EmptyStmt
        case _: AbstractDomainFuncApp => Statements.EmptyStmt
      }
      case _ =>
        Statements.EmptyStmt
    }
  }

  def searchVarName(decClause: Exp): Seq[LocalVarDecl] = {
    decClause match {
      case a: AbstractLocalVar => Seq(LocalVarDecl(a.name, a.typ)(a.pos, a.info))
      case e: BinExp => searchVarName(e.left) ++ searchVarName(e.right)
      case e: UnExp => searchVarName(e.exp)
      case ap: AccessPredicate => ap match {
        case FieldAccessPredicate(loc, perm) => searchVarName(ap.loc)
        case PredicateAccessPredicate(loc, perm) => searchVarName(ap.loc)
      } //a.subExps a.whenExhaling TODO
      //    case InhaleExhaleExp(in, ex) =>
      //    case _: PermExp =>
      case la: LocationAccess => la match {
        case FieldAccess(rcv, field) => searchVarName(rcv)
        case PredicateAccess(args, predicateName) =>
          //TODO implement better
          var s = Seq()
          args.foreach(arg => s ++ searchVarName(arg))
          s
      }
      //    case CondExp(cond, thn, els) =>
      case Unfolding(acc, body) => searchVarName(acc) ++ searchVarName(body)
      //    case _: GhostOperation =>
      //    case Let(variable, exp, body) =>
      //    case _: QuantifiedExp =>
      //    case ForPerm(variable, accessList, body) =>
      //case s: SeqExp => s.
      //    case _: SetExp =>
      //    case _: MultisetExp =>
      //    case _: Literal =>
      case pt: PossibleTrigger => pt match {
        case FuncApp(funcname, args) => (args map (a => searchVarName(a))).flatten
        case DomainFuncApp(funcname, args, typVarMap) => (args map (a => searchVarName(a))).flatten
        case s: SeqExp =>
          s match {
            case _: EmptySeq => Seq()
            case ExplicitSeq(elems) => (elems map (e => searchVarName(e))).flatten
            case RangeSeq(low, high) => searchVarName(low) ++ searchVarName(high)
            case SeqAppend(left, right) => searchVarName(left) ++ searchVarName(right)
            case SeqIndex(s, idx) => searchVarName(s) ++ searchVarName(idx)
            case SeqTake(s, n) => searchVarName(s) ++ searchVarName(n)
            case SeqDrop(s, n) => searchVarName(s) ++ searchVarName(n)
            case SeqContains(elem, s) => searchVarName(elem) ++ searchVarName(s)
            case SeqUpdate(s, idx, elem) => searchVarName(s) ++ searchVarName(idx) ++ searchVarName(elem)
            case SeqLength(s) => searchVarName(s)
          }
        case set: SetExp => set match {
          case _: AnySetExp => throw new Exception("TODO - AnySetExpr")
          case EmptySet(elemTyp) => Seq()
          case ExplicitSet(elems) => (elems map (e => searchVarName(e))).flatten
        }
        case ms: MultisetExp => ms match {
          case _: AnySetExp => throw new Exception("TODO - AnySetExpr")
          case EmptyMultiset(elemTyp) => Seq()
          case ExplicitMultiset(elems) => (elems map (e => searchVarName(e))).flatten
        }
      }
      //    case _: ForbiddenInTrigger =>
      //    case _: FuncLikeApp =>
      //case lhs: Lhs => lhs match {
      //case FieldAccess(rcv, field) => searchVarName(rcv)
      //case LocalVar(name) => Seq(LocalVarDecl(a.name, a.typ)(a.pos, a.info))
      //}
      case _ => Seq()
    }
  }

  def rewriteExpr(expr: Exp, newExpr: Map[String, Exp]): Exp = {
    expr match {
      case k: AbstractLocalVar =>
        newExpr(k.name)
      case binary: BinExp =>
        binary match {
          case e: Add => Add(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e: Sub => Sub(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e: Mul => Mul(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e: Div => Div(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
          case e: Mod => Mod(rewriteExpr(e.left, newExpr), rewriteExpr(e.right, newExpr))(binary.pos)
        }
      case unary: UnExp =>
        unary match {
          case e: Minus => Minus(rewriteExpr(e.exp, newExpr))(unary.pos)
          //case PermMinus(exp) =>
        }
      case a: AccessPredicate => a match {
        case FieldAccessPredicate(loc, perm) => FieldAccessPredicate(loc, rewriteExpr(perm, newExpr))(a.pos)
        case PredicateAccessPredicate(loc, perm) =>
          val predAcc = rewriteExpr(loc, newExpr).asInstanceOf[PredicateAccess]
          PredicateAccessPredicate(predAcc, perm)(a.pos)
      }
      //    case InhaleExhaleExp(in, ex) =>
      //    case _: PermExp =>
      case la: LocationAccess => la match {
        case FieldAccess(rcv, field) => FieldAccess(rewriteExpr(rcv, newExpr), field)(la.pos)
        case PredicateAccess(args, predicateName) =>
          val arg = args map (e => rewriteExpr(e, newExpr))
          PredicateAccess(arg, predicateName)(la.pos, la.info, la.errT) //TODO why info and err?
      }
      //    case CondExp(cond, thn, els) =>
      case u: Unfolding =>

        var body = rewriteExpr(u.body, newExpr)
        var pred = rewriteExpr(u.acc, newExpr).asInstanceOf[PredicateAccessPredicate]
        Unfolding(pred, body)(u.pos)
      //    case _: GhostOperation =>
      //    case Let(variable, exp, body) =>
      //    case _: QuantifiedExp =>
      //    case ForPerm(variable, accessList, body) =>
      //    case _: AbstractLocalVar =>
      //    case _: SeqExp =>
      //    case _: SetExp =>
      //    case _: MultisetExp =>
      //    case _: Literal =>
      case pt: PossibleTrigger => pt match {
        case fa: FuncApp =>
          val arg = fa.args map (e => rewriteExpr(e, newExpr))
          FuncApp(fa.funcname, arg)(fa.pos, fa.info, fa.typ, fa.formalArgs, fa.errT)
        case dfa: DomainFuncApp =>
          val arg = dfa.args map (e => rewriteExpr(e, newExpr))
          DomainFuncApp(dfa.funcname, arg, dfa.typVarMap)(dfa.pos, dfa.info, dfa.typ, dfa.formalArgs, dfa.domainName, dfa.errT)
        case seq: SeqExp => seq match {
          case EmptySeq(elemTyp) => EmptySeq(elemTyp)(seq.pos)
          case ExplicitSeq(elems) => ExplicitSeq(elems map (e => rewriteExpr(e, newExpr)))(seq.pos)
          case RangeSeq(low, high) => RangeSeq(rewriteExpr(low, newExpr), rewriteExpr(high, newExpr))(seq.pos)
          case SeqAppend(left, right) => SeqAppend(rewriteExpr(left, newExpr), rewriteExpr(right, newExpr))(seq.pos)
          case SeqIndex(s, idx) => SeqIndex(rewriteExpr(s, newExpr), rewriteExpr(idx, newExpr))(seq.pos)
          case SeqTake(s, n) => SeqTake(rewriteExpr(s, newExpr), rewriteExpr(n, newExpr))(seq.pos)
          case SeqDrop(s, n) => SeqDrop(rewriteExpr(s, newExpr), rewriteExpr(n, newExpr))(seq.pos)
          case SeqContains(elem, s) => SeqContains(rewriteExpr(elem, newExpr), rewriteExpr(s, newExpr))(seq.pos)
          case SeqUpdate(s, idx, elem) => SeqUpdate(rewriteExpr(s, newExpr), rewriteExpr(idx, newExpr), rewriteExpr(elem, newExpr))(seq.pos)
          case SeqLength(s) => SeqLength(rewriteExpr(s, newExpr))(seq.pos)
        }
        case set: SetExp => set match {
          case a: AnySetExp => a
          case EmptySet(elemTyp) => EmptySet(elemTyp)(set.pos)
          case ExplicitSet(elems) => ExplicitSet(elems map (e => rewriteExpr(e, newExpr)))(set.pos)
        }
        case mSet: MultisetExp => mSet match {
          case a: AnySetExp => a
          case EmptyMultiset(elemTyp) => EmptyMultiset(elemTyp)(mSet.pos)
          case ExplicitMultiset(elems) => ExplicitMultiset(elems map (e => rewriteExpr(e, newExpr)))(mSet.pos)
        }


      }
      //    case _: ForbiddenInTrigger =>
      //    case _: FuncLikeApp =>
      //    case _: BinExp =>
      //    case _: UnExp =>
      //    case _: Lhs =>
      case default => default
    }
  }

  def addOldIfNecessary(head: Exp): Exp = {
    head match {
      case unfold: Unfolding => Old(unfold)(unfold.pos)
      case default => default
    }
  }


  //conjuction = true => Or
  //conjuction = false => And
  def buildDecTree(decrFuncS: Seq[Exp], conj: Boolean): Exp = {
    if(decrFuncS.size == 1)
      decrFuncS.head
    else if(conj)
      Or(decrFuncS.head, buildDecTree(decrFuncS.tail, false))(decrFuncS.head.pos)
    else
      And(decrFuncS.head, buildDecTree(decrFuncS.tail, true))(decrFuncS.head.pos)
  }

  def buildBoundTree(decrFuncS: Seq[Exp]): Exp = {
    if(decrFuncS.size == 1)
      decrFuncS.head
    else
      And(decrFuncS.head, buildBoundTree(decrFuncS.tail))(decrFuncS.head.pos)
  }


  //  def test(body: Exp): Exp = body match {
  //    case a: AccessPredicate => a match {
  //      case a: FieldAccessPredicate => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PredicateAccessPredicate => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //    }
  //    case a: InhaleExhaleExp => a match {
  //      case _ => //could not find inherited objects or case classes
  //    }
  //    case a: PermExp => a match {
  //      case a: WildcardPerm => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: EpsilonPerm => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: FractionalPerm => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PermDiv => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: CurrentPerm => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PermMinus => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PermAdd => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PermSub => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PermMul => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: IntPermMul => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: AbstractConcretePerm => a match {
  //        case a: FullPerm => a match {
  //          case _ => //could not find inherited objects or case classes
  //        }
  //        case a: NoPerm => a match {
  //          case _ => //could not find inherited objects or case classes
  //        }
  //      }
  //    }
  //    case a: LocationAccess => a match {
  //      case FieldAccess(rcv, field) =>
  //      case PredicateAccess(args, predicateName) =>
  //    }
  //    case a: CondExp => a match {
  //      case _ => //could not find inherited objects or case classes
  //    }
  //    case a: Unfolding => a match {
  //      case _ => //could not find inherited objects or case classes
  //    }
  //    case a: GhostOperation => a match {
  //      case a: UnfoldingGhostOp => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: FoldingGhostOp => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: ApplyingGhostOp => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: PackagingGhostOp => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //    }
  //    case a: Let => a match {
  //      case _ => //could not find inherited objects or case classes
  //    }
  //    case a: QuantifiedExp => a match {
  //      case a: Forall => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: Exists => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: ForPerm => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //    }
  //    case a: ForPerm => a match {
  //      case _ => //could not find inherited objects or case classes
  //    }
  //    case a: AbstractLocalVar => a match {
  //      case a: LocalVar => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: Result => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //    }
  //    case a: SeqExp => a match {
  //      case a: EmptySeq => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: ExplicitSeq => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: RangeSeq => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqAppend => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqIndex => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqTake => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqDrop => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqContains => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqUpdate => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //      case a: SeqLength => a match {
  //        case _ => //could not find inherited objects or case classes
  //      }
  //    }
  //    case a: SetExp => a match {
  //      case a: AnySetExp => a match {
  //        case a: AnySetUnExp => a match {
  //          case a: AnySetCardinality => a match {
  //            case _ => //could not find inherited objects or case classes
  //          }
  //        }
  //        case a: AnySetBinExp => a match {
  //          case AnySetUnion(left, right) =>
  //          case AnySetIntersection(left, right) =>
  //          case AnySetSubset(left, right) =>
  //          case AnySetMinus(left, right) =>
  //          case AnySetContains(elem, s) =>
  //        }
  //      }
  //      case a: EmptySet =>
  //      case a: ExplicitSet =>
  //    }
  //    case a: MultisetExp => a match {
  //      case _: AnySetExp =>
  //      case EmptyMultiset(elemTyp) =>
  //      case ExplicitMultiset(elems) =>
  //    }
  //    case a: Literal => a match {
  //      case IntLit(i) =>
  //      case _: BoolLit =>
  //      case NullLit() =>
  //    }
  //    case a: PossibleTrigger => a match {
  //      case FuncApp(funcname, args) =>
  //      case DomainFuncApp(funcname, args, typVarMap) =>
  //      case _: SeqExp =>
  //      case _: SetExp =>
  //      case _: MultisetExp =>
  //    }
  //    case a: ForbiddenInTrigger => a match {
  //      case CondExp(cond, thn, els) =>
  //      case _: DomainOpExp =>
  //    }
  //    case a: FuncLikeApp => a match {
  //      case FuncApp(funcname, args) =>
  //      case _: AbstractDomainFuncApp =>
  //    }
  //    case a: BinExp => a match {
  //      case _: AnySetBinExp =>
  //      case _: EqualityCmp =>
  //      case _: DomainBinExp =>
  //    }
  //    case a: UnExp => a match {
  //      case _: OldExp =>
  //      case _: AnySetUnExp =>
  //      case _: DomainUnExp =>
  //    }
  //    case a: Lhs => a match {
  //      case FieldAccess(rcv, field) =>
  //      case LocalVar(name) =>
  //    }
  //  }
}