/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

/* TODO: This is basically a copy of silver.ast.utility.Transformer. Can we share code?
 *       This could be done by using tree visiting and rewriting functionality from Kiama,
  *      or to implement something generic ourselves. Shapeless or Scala Macros might be
  *      useful because they might help us to abstract over arity when it comes to
  *      copying existing nodes, i.e., case classes.
 */
object Transformer {
  /* Attention: You most likely want to call initTree on the transformed node. */
  def transform[A <: PNode](node: A,
                            pre: PartialFunction[PNode, PNode] = PartialFunction.empty)(
                             recursive: PNode => Boolean = !pre.isDefinedAt(_),
                             post: PartialFunction[PNode, PNode] = PartialFunction.empty,
                             allowChangingNodeType: Boolean = false,
                             resultCheck: PartialFunction[(PNode, PNode), Unit] = PartialFunction.empty): A = {

    @inline
    def go[B <: PNode](root: B): B = {
      transform(root, pre)(recursive, post, allowChangingNodeType, resultCheck)
    }

    def recurse(parent: PNode): PNode = {
      val newNode = parent match {
        case PMacroRef(idnuse) => PMacroRef(go(idnuse))
        case _: PIdnDef => parent
        case _: PIdnUse => parent
        case PFormalArgDecl(idndef, typ) => PFormalArgDecl(go(idndef), go(typ))
        case PTypeVarDecl(idndef) => PTypeVarDecl(go(idndef))
        case _: PPrimitiv => parent
        case pdt@PDomainType(domain, args) =>
          val newPdt = PDomainType(go(domain), args map go)
          newPdt.kind = pdt.kind
          newPdt
        case PSeqType(elementType) => PSeqType(go(elementType))
        case PSetType(elementType) => PSetType(go(elementType))
        case PMultisetType(elementType) => PMultisetType(go(elementType))
        case _: PUnknown => parent
        case _: PPredicateType | _: PWandType => parent

        case PBinExp(left, op, right) => PBinExp(go(left), op, go(right))
        case PUnExp(op, exp) => PUnExp(op, go(exp))
        case _: PIntLit => parent
        case _: PResultLit => parent
        case _: PBoolLit => parent
        case _: PNullLit => parent
        case PFieldAccess(rcv, idnuse) => PFieldAccess(go(rcv), go(idnuse))
        case PPredicateAccess(args, idnuse) => PPredicateAccess(args map go, go(idnuse))
        case PCall(func, args, explicitType) =>
          PCall(go(func), args map go, explicitType match {
            case Some(t) => Some(go(t))
            case None => None
          })


        case PUnfolding(acc, exp) => PUnfolding(go(acc), go(exp))
        case PApplying(wand, exp) => PApplying(go(wand), go(exp))

        case PExists(vars, exp) => PExists(vars map go, go(exp))
        case PForall(vars, triggers, exp) => PForall(vars map go, triggers map go, go(exp))
        case PTrigger(exp) => PTrigger(exp map go)
        case PForPerm(v, fields, exp) => PForPerm(go(v), fields map go, go(exp))
        case PCondExp(cond, thn, els) => PCondExp(go(cond), go(thn), go(els))
        case PInhaleExhaleExp(in, ex) => PInhaleExhaleExp(go(in), go(ex))
        case PCurPerm(loc) => PCurPerm(go(loc))
        case _: PNoPerm => parent
        case _: PFullPerm => parent
        case _: PWildcard => parent
        case _: PEpsilon => parent
        case PAccPred(loc, perm) => PAccPred(go(loc), go(perm))
        case POld(e) => POld(go(e))
        case PLabelledOld(lbl, e) => PLabelledOld(go(lbl), go(e))
        case PEmptySeq(t) => PEmptySeq(go(t))
        case PExplicitSeq(elems) => PExplicitSeq(elems map go)
        case PRangeSeq(low, high) => PRangeSeq(go(low), go(high))
        case PSeqIndex(seq, idx) => PSeqIndex(go(seq), go(idx))
        case PSeqTake(seq, n) => PSeqTake(go(seq), go(n))
        case PSeqDrop(seq, n) => PSeqDrop(go(seq), go(n))
        case PSeqUpdate(seq, idx, elem) => PSeqUpdate(go(seq), go(idx), go(elem))
        case PSize(seq) => PSize(go(seq))
        case PEmptySet(t) => PEmptySet(go(t))
        //        case _: PEmptySet => parent
        case PExplicitSet(elems) => PExplicitSet(elems map go)
        case PEmptyMultiset(t) => PEmptyMultiset(go(t))
        //        case _: PEmptyMultiset => parent
        case PExplicitMultiset(elems) => PExplicitMultiset(elems map go)

        case PSeqn(ss) => PSeqn(ss map go)
        case PFold(e) => PFold(go(e))
        case PUnfold(e) => PUnfold(go(e))
        case PPackageWand(e, proofScript) => PPackageWand(go(e), go(proofScript))
        case PApplyWand(e) => PApplyWand(go(e))
        case PExhale(e) => PExhale(go(e))
        case PAssert(e) => PAssert(go(e))
        case PAssume(e) => PAssume(go(e))
        case PInhale(e) => PInhale(go(e))
        case PNewStmt(target, fields) => PNewStmt(go(target), fields map (_.map(go)))
        case PVarAssign(idnuse, rhs) => PVarAssign(go(idnuse), go(rhs))
        case PFieldAssign(fieldAcc, rhs) => PFieldAssign(go(fieldAcc), go(rhs))
        case PIf(cond, thn, els) => PIf(go(cond), go(thn), go(els))
        case PWhile(cond, invs, body) => PWhile(go(cond), invs map go, go(body))
        case PFresh(vars) => PFresh(vars map go)
        case PConstraining(vars, stmt) => PConstraining(vars map go, go(stmt))
        case PLocalVarDecl(idndef, typ, init) => PLocalVarDecl(go(idndef), go(typ), init map go)
        case PMethodCall(targets, method, args) => PMethodCall(targets map go, go(method), args map go)
        case PLabel(idndef, invs) => PLabel(go(idndef), invs map go)
        case PGoto(target) => PGoto(go(target))
        case PDefine(idndef, optArgs, exp) => PDefine(go(idndef), optArgs map (_ map go) , go(exp))
        case PLet(exp, nestedScope) => PLet(go(exp), go(nestedScope))
        case PLetNestedScope(idndef, body) => PLetNestedScope(go(idndef), go(body))
        case _: PSkip => parent

        case PProgram(files, macros, domains, fields, functions, predicates, methods, errors) => PProgram(files, macros map go, domains map go, fields map go, functions map go, predicates map go, methods map go, errors)
        case PImport(file) => PImport(file)
        case PMethod(idndef, formalArgs, formalReturns, pres, posts, body) => PMethod(go(idndef), formalArgs map go, formalReturns map go, pres map go, posts map go,
          go(body))
        case PDomain(idndef, typVars, funcs, axioms) => PDomain(go(idndef), typVars map go, funcs map go, axioms map go)
        case PField(idndef, typ) => PField(go(idndef), go(typ))
        case PFunction(idndef, formalArgs, typ, pres, posts, body) => PFunction(go(idndef), formalArgs map go, go(typ), pres map go, posts map go, body map go)
        case pdf@PDomainFunction(idndef, formalArgs, typ, unique) => PDomainFunction(go(idndef), formalArgs map go, go(typ), unique)(domainName = pdf.domainName)
        case PPredicate(idndef, formalArgs, body) => PPredicate(go(idndef), formalArgs map go, body map go)
        case pda@PAxiom(idndef, exp) => PAxiom(go(idndef), go(exp))(domainName = pda.domainName)
      }

      if (!allowChangingNodeType)
        assert(newNode.getClass == parent.getClass, "Transformer is not expected to change type of nodes.")

      newNode.setPos(parent)
    }



    val beforeRecursion = pre.applyOrElse(node, identity[PNode])

    resultCheck.applyOrElse((node, beforeRecursion), identity[(PNode, PNode)])

    val afterRecursion = if (recursive(node)) {
      recurse(beforeRecursion)
    } else {
      beforeRecursion
    }
    post.applyOrElse(afterRecursion, identity[PNode]).asInstanceOf[A]
  }

  def parseTreeDuplicator: PartialFunction[(PNode, Seq[Any]), PNode] = {
    case (p: PMacroRef, Seq(idndef: PIdnUse)) => PMacroRef(idndef)
    case (p: PIdnDef, _) => p
    case (p: PIdnUse, _) => p
    case (p: PFormalArgDecl, Seq(idndef: PIdnDef, typ: PType)) => PFormalArgDecl(idndef, typ)
    case (p: PTypeVarDecl, Seq(idndef: PIdnDef)) => PTypeVarDecl(idndef)
    case (p: PPrimitiv, _) => p
    case (p: PDomainType, Seq(domain: PIdnUse, args: Seq[PType@unchecked])) => PDomainType(domain, args)
    case (p: PSeqType, Seq(elementType: PType)) => PSeqType(elementType)
    case (p: PSetType, Seq(elementType: PType)) => PSetType(elementType)
    case (p: PMultisetType, Seq(elementType: PType)) => PMultisetType(elementType)
    case (p: PUnknown, _) => p
    case (p: PPredicateType, _) => p
    case (p: PWandType, _) => p

    case (p: PBinExp, Seq(left: PExp, right: PExp)) => PBinExp(left, p.opName, right)
    case (p: PUnExp, Seq(exp: PExp)) => PUnExp(p.opName, exp)
    case (p: PTrigger, Seq(exp: Seq[PExp@unchecked])) => PTrigger(exp)
    case (p: PIntLit, _) => p
    case (p: PResultLit, _) => p
    case (p: PBoolLit, _) => p
    case (p: PNullLit, _) => p
    case (p: PFieldAccess, Seq(rcv: PExp, idnuse: PIdnUse)) => PFieldAccess(rcv, idnuse)
    case (p: PPredicateAccess, Seq(args: Seq[PExp@unchecked], idnuse: PIdnUse)) => PPredicateAccess(args, idnuse)
    case (p: PCall, Seq(func: PIdnUse, args: Seq[PExp@unchecked], explicitType: Option[PType@unchecked])) => PCall(func, args, explicitType)

    case (p: PUnfolding, Seq(acc: PAccPred, exp: PExp)) => PUnfolding(acc, exp)
    case (p: PApplying, Seq(wand: PExp, exp: PExp)) => PApplying(wand, exp)

    case (p: PExists, Seq(vars: Seq[PFormalArgDecl@unchecked], exp: PExp)) => PExists(vars, exp)
    case (p: PForall, Seq(vars: Seq[PFormalArgDecl@unchecked], triggers: Seq[PTrigger@unchecked], exp: PExp)) => PForall(vars, triggers, exp)
    case (p: PForPerm, Seq(v: PFormalArgDecl, fields: Seq[PIdnUse@unchecked], exp: PExp)) => PForPerm(v, fields, exp)
    case (p: PCondExp, Seq(cond: PExp, thn: PExp, els: PExp)) => PCondExp(cond, thn, els)
    case (p: PInhaleExhaleExp, Seq(in: PExp, ex: PExp)) => PInhaleExhaleExp(in, ex)
    case (p: PCurPerm, Seq(loc: PLocationAccess)) => PCurPerm(loc)
    case (p: PNoPerm, _) => p
    case (p: PFullPerm, _) => p
    case (p: PWildcard, _) => p
    case (p: PEpsilon, _) => p
    case (p: PAccPred, Seq(loc: PLocationAccess, perm: PExp)) => PAccPred(loc, perm)
    case (p: POld, Seq(e: PExp)) => POld(e)
    case (p: PLabelledOld, Seq(lbl: PIdnUse, e: PExp)) => PLabelledOld(lbl, e)
    case (p: PEmptySeq, Seq(t: PType)) => PEmptySeq(t)
    case (p: PExplicitSeq, Seq(elems: Seq[PExp@unchecked])) => PExplicitSeq(elems)
    case (p: PRangeSeq, Seq(low: PExp, high: PExp)) => PRangeSeq(low, high)
    case (p: PSeqIndex, Seq(seq: PExp, idx: PExp)) => PSeqIndex(seq, idx)
    case (p: PSeqTake, Seq(seq: PExp, n: PExp)) => PSeqTake(seq, n)
    case (p: PSeqDrop, Seq(seq: PExp, n: PExp)) => PSeqDrop(seq, n)
    case (p: PSeqUpdate, Seq(seq: PExp, idx: PExp, elem: PExp)) => PSeqUpdate(seq, idx, elem)
    case (p: PSize, Seq(seq: PExp)) => PSize(seq)
    case (p: PEmptySet, Seq(t: PType)) => PEmptySet(t)
    case (p: PExplicitSet, Seq(elems: Seq[PExp@unchecked])) => PExplicitSet(elems)
    case (p: PEmptyMultiset, Seq(t: PType)) => PEmptyMultiset(t)
    case (p: PExplicitMultiset, Seq(elems: Seq[PExp@unchecked])) => PExplicitMultiset(elems)

    case (p: PSeqn, Seq(ss: Seq[PStmt@unchecked])) => PSeqn(ss)
    case (p: PFold, Seq(e: PExp)) => PFold(e)
    case (p: PUnfold, Seq(e: PExp)) => PUnfold(e)
    case (p: PPackageWand, Seq(e: PExp, proofScript: PSeqn)) => PPackageWand(e, proofScript)
    case (p: PApplyWand, Seq(e: PExp)) => PApplyWand(e)
    case (p: PExhale, Seq(e: PExp)) => PExhale(e)
    case (p: PAssert, Seq(e: PExp)) => PAssert(e)
    case (p: PAssume, Seq(e: PExp)) => PAssume(e)
    case (p: PInhale, Seq(e: PExp)) => PInhale(e)
    case (p: PNewStmt, Seq(target: PIdnUse, fields: Seq[PIdnUse@unchecked])) => PNewStmt(target, if (fields.length == 0) None else Some(fields))
    case (p: PVarAssign, Seq(idnuse: PIdnUse, rhs: PExp)) => PVarAssign(idnuse, rhs)
    case (p: PFieldAssign, Seq(fieldAcc: PFieldAccess, rhs: PExp)) => PFieldAssign(fieldAcc, rhs)
    case (p: PIf, Seq(cond: PExp, thn: PSeqn, els: PSeqn)) => PIf(cond, thn, els)
    case (p: PWhile, Seq(cond: PExp, invs: Seq[PExp@unchecked], body: PSeqn)) => PWhile(cond, invs, body)
    case (p: PFresh, Seq(vars: Seq[PIdnUse@unchecked])) => PFresh(vars)
    case (p: PConstraining, Seq(vars: Seq[PIdnUse@unchecked], stmt: PSeqn)) => PConstraining(vars, stmt)
    case (p: PLocalVarDecl, Seq(idndef: PIdnDef, typ: PType, init: Option[PExp@unchecked])) => PLocalVarDecl(idndef, typ, init)
    case (p: PMethodCall, Seq(targets: Seq[PIdnUse@unchecked], method: PIdnUse, args: Seq[PExp@unchecked])) => PMethodCall(targets, method, args)
    case (p: PLabel, Seq(idndef: PIdnDef, invs: Seq[PExp@unchecked])) => PLabel(idndef, invs)
    case (p: PGoto, Seq(target: PIdnUse)) => PGoto(target)
    case (p: PDefine, Seq(idndef: PIdnDef, optArgs: Seq[PIdnDef@unchecked], exp: PExp)) => PDefine(idndef, if (optArgs.length == 0) None else Some(optArgs), exp)
    case (p: PLet, Seq(exp: PExp, nestedScope: PLetNestedScope)) => PLet(exp, nestedScope)
    case (p: PLetNestedScope, Seq(idndef: PFormalArgDecl, body: PExp)) => PLetNestedScope(idndef, body)
    case (p: PSkip, _) => p

    case (p: PProgram, Seq(files: Seq[PImport@unchecked], macros: Seq[PDefine@unchecked], domains: Seq[PDomain@unchecked], fields: Seq[PField@unchecked], functions: Seq[PFunction@unchecked], predicates: Seq[PPredicate@unchecked], methods: Seq[PMethod@unchecked])) =>
      PProgram(files, macros, domains, fields, functions, predicates, methods, p.errors)

    case (p: PImport, _) => p
    case (p: PMethod, Seq(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl@unchecked], formalReturns: Seq[PFormalArgDecl@unchecked], pres: Seq[PExp@unchecked], posts: Seq[PExp@unchecked], body: PStmt)) => PMethod(idndef, formalArgs, formalReturns, pres, posts, body)
    case (p: PDomain, Seq(idndef: PIdnDef, typVars: Seq[PTypeVarDecl@unchecked], funcs: Seq[PDomainFunction@unchecked], axioms: Seq[PAxiom@unchecked])) => PDomain(idndef, typVars, funcs, axioms)
    case (p: PField, Seq(idndef: PIdnDef, typ: PType)) => PField(idndef, typ)
    case (p: PFunction, Seq(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl@unchecked], typ: PType, pres: Seq[PExp@unchecked], posts: Seq[PExp@unchecked], body: Option[PExp@unchecked])) => PFunction(idndef, formalArgs, typ, pres, posts, body)
    case (p: PDomainFunction, Seq(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl@unchecked], typ: PType)) => PDomainFunction(idndef, formalArgs, typ, p.unique)(domainName = p.domainName)
    case (p: PPredicate, Seq(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl@unchecked], body: Option[PExp@unchecked])) => PPredicate(idndef, formalArgs, body)
    case (p: PAxiom, Seq(idndef: PIdnDef, exp: PExp)) => PAxiom(idndef, exp)(domainName = p.domainName)

    case (p: PNode, s) =>
      throw new Exception("Not able to duplicate: " + p + " with children: " + s)
  }
}
