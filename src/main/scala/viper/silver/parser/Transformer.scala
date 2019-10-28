// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

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
        case PMagicWandExp(left, right) => PMagicWandExp(go(left), go(right))
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

        case PExists(vars, triggers, exp) => PExists(vars map go, triggers map go, go(exp))
        case PForall(vars, triggers, exp) => PForall(vars map go, triggers map go, go(exp))
        case PTrigger(exp) => PTrigger(exp map go)
        case PForPerm(vars, res, exp) => PForPerm(vars map go, go(res), go(exp))
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
        case PLocalVarDecl(idndef, typ, init) => PLocalVarDecl(go(idndef), go(typ), init map go)
        case PMethodCall(targets, method, args) => PMethodCall(targets map go, go(method), args map go)
        case PLabel(idndef, invs) => PLabel(go(idndef), invs map go)
        case PGoto(target) => PGoto(go(target))
        case PDefine(idndef, optArgs, exp) => PDefine(go(idndef), optArgs map (_ map go) , go(exp))
        case PLet(exp, nestedScope) => PLet(go(exp), go(nestedScope))
        case PLetNestedScope(idndef, body) => PLetNestedScope(go(idndef), go(body))
        case _: PSkip => parent

        case PProgram(files, macros, domains, fields, functions, predicates, methods, errors) => PProgram(files, macros map go, domains map go, fields map go, functions map go, predicates map go, methods map go, errors)
        case PLocalImport(file) => PLocalImport(file)
        case PStandardImport(file) => PStandardImport(file)
        case PMethod(idndef, formalArgs, formalReturns, pres, posts, body) => PMethod(go(idndef), formalArgs map go, formalReturns map go, pres map go, posts map go, body map go)
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

  case class ParseTreeDuplicationError(original: PNode, newChildren: Seq[Any])
      extends RuntimeException(s"Cannot duplicate $original with new children $newChildren")
}
