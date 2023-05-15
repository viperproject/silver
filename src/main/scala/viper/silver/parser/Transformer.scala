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
    @inline
    def goPair[B <: PNode, C <: PNode](root: (B, C)): (B, C) = {
      (go(root._1), go(root._2))
    }

    def recurse(parent: PNode): PNode = {
      val newNode = parent match {
        case p@PMacroRef(idnuse) => PMacroRef(go(idnuse))(p.pos)
        case _: PIdnDef => parent
        case _: PIdnUse => parent
        case p@PFormalArgDecl(idndef, typ) => PFormalArgDecl(go(idndef), go(typ))(p.pos)
        case p@PTypeVarDecl(idndef) => PTypeVarDecl(go(idndef))(p.pos)
        case p@PPrimitiv(keyword) => PPrimitiv(go(keyword))(p.pos)
        case pdt@PDomainType(domain, args) =>
          val newPdt = PDomainType(go(domain), args map go)(pdt.pos)
          newPdt.kind = pdt.kind
          newPdt
        case p@PSeqType(seq, elementType) => PSeqType(go(seq), go(elementType))(p.pos)
        case p@PSetType(set, elementType) => PSetType(go(set), go(elementType))(p.pos)
        case p@PMultisetType(multiset, elementType) => PMultisetType(go(multiset), go(elementType))(p.pos)
        case p@PMapType(map, keyType, valueType) => PMapType(map, go(keyType), go(valueType))(p.pos)
        case _: PUnknown => parent
        case _: PPredicateType | _: PWandType => parent
        case p@PMagicWandExp(left, op, right) => PMagicWandExp(go(left), go(op), go(right))(p.pos)
        case p@PBinExp(left, op, right) => PBinExp(go(left), go(op), go(right))(p.pos)
        case p@PUnExp(op, exp) => PUnExp(go(op), go(exp))(p.pos)
        case _: PIntLit => parent
        case p@PResultLit(result) => PResultLit(go(result))(p.pos)
        case p@PBoolLit(keyword, b) => PBoolLit(go(keyword), b)(p.pos)
        case p@PNullLit(nul) => PNullLit(go(nul))(p.pos)
        case p@PFieldAccess(rcv, idnuse) => PFieldAccess(go(rcv), go(idnuse))(p.pos)
        case p@PPredicateAccess(args, idnuse) => PPredicateAccess(args map go, go(idnuse))(p.pos)
        case p@PCall(func, args, explicitType) =>
          PCall(go(func), args map go, explicitType match {
            case Some(t) => Some(go(t))
            case None => None
          })(p.pos)


        case p@PUnfolding(unfolding, acc, exp) => PUnfolding(go(unfolding), go(acc), go(exp))(p.pos)
        case p@PApplying(applying, wand, exp) => PApplying(go(applying), go(wand), go(exp))(p.pos)

        case p@PExists(exists, vars, triggers, exp) => PExists(go(exists), vars map go, triggers map go, go(exp))(p.pos)
        case p@PForall(forall, vars, triggers, exp) => PForall(go(forall), vars map go, triggers map go, go(exp))(p.pos)
        case p@PTrigger(exp) => PTrigger(exp map go)(p.pos)
        case p@PForPerm(forperm, vars, res, exp) => PForPerm(go(forperm), vars map go, go(res), go(exp))(p.pos)
        case p@PCondExp(cond, q, thn, c, els) => PCondExp(go(cond), go(q), go(thn), go(c), go(els))(p.pos)
        case p@PInhaleExhaleExp(in, ex) => PInhaleExhaleExp(go(in), go(ex))(p.pos)
        case p@PCurPerm(loc) => PCurPerm(go(loc))(p.pos)
        case _: PNoPerm => parent
        case _: PFullPerm => parent
        case _: PWildcard => parent
        case _: PEpsilon => parent
        case p@PAccPred(acc, loc, perm) => PAccPred(go(acc), go(loc), go(perm))(p.pos)
        case p@POld(e) => POld(go(e))(p.pos)
        case p@PLabelledOld(lbl, e) => PLabelledOld(go(lbl), go(e))(p.pos)
        case p@PEmptySeq(t) => PEmptySeq(go(t))(p.pos)
        case p@PExplicitSeq(elems) => PExplicitSeq(elems map go)(p.pos)
        case p@PRangeSeq(low, high) => PRangeSeq(go(low), go(high))(p.pos)
        case p@PSeqIndex(seq, idx) => PSeqIndex(go(seq), go(idx))(p.pos)
        case p@PSeqTake(seq, n) => PSeqTake(go(seq), go(n))(p.pos)
        case p@PSeqDrop(seq, n) => PSeqDrop(go(seq), go(n))(p.pos)
        case p@PSeqUpdate(seq, idx, elem) => PSeqUpdate(go(seq), go(idx), go(elem))(p.pos)
        case p@PSize(seq) => PSize(go(seq))(p.pos)
        case p@PEmptySet(t) => PEmptySet(go(t))(p.pos)
        case p@PLookup(seq, idx) => PLookup(go(seq), go(idx))(p.pos)
        case p@PUpdate(seq, idx, elem) => PUpdate(go(seq), go(idx), go(elem))(p.pos)
        case p@PExplicitSet(elems) => PExplicitSet(elems map go)(p.pos)
        case p@PEmptyMultiset(t) => PEmptyMultiset(go(t))(p.pos)
        case p@PExplicitMultiset(elems) => PExplicitMultiset(elems map go)(p.pos)

        case p@PSeqn(ss) => PSeqn(ss map go)(p.pos)
        case p@PFold(e) => PFold(go(e))(p.pos)
        case p@PUnfold(e) => PUnfold(go(e))(p.pos)
        case p@PPackageWand(pckg, e, proofScript) => PPackageWand(go(pckg), go(e), go(proofScript))(p.pos)
        case p@PApplyWand(apply, e) => PApplyWand(go(apply), go(e))(p.pos)
        case p@PExhale(exhale, e) => PExhale(go(exhale), go(e))(p.pos)
        case p@PAssert(assert, e) => PAssert(go(assert), go(e))(p.pos)
        case p@PAssume(assume, e) => PAssume(go(assume), go(e))(p.pos)
        case p@PInhale(inhale, e) => PInhale(go(inhale), go(e))(p.pos)
        case p@PQuasihavoc(quasihavoc, lhs, e) =>
          PQuasihavoc(go(quasihavoc), lhs map goPair, go(e))(p.pos)
        case p@PQuasihavocall(quasihavocall, vars, cc, lhs, e) =>
          PQuasihavocall(go(quasihavocall), vars map go, go(cc), lhs map goPair, go(e))(p.pos)
        case p@PEmptyMap(keyType, valueType) => PEmptyMap(go(keyType), go(valueType))(p.pos)
        case p@PExplicitMap(exprs) => PExplicitMap(exprs map go)(p.pos)
        case p@PMaplet(key, value) => PMaplet(go(key), go(value))(p.pos)
        case p@PMapDomain(base) => PMapDomain(go(base))(p.pos)
        case p@PMapRange(base) => PMapRange(go(base))(p.pos)
        case PNewStmt(target, fields) => PNewStmt(go(target), fields map (_.map(go)))
        case p@PVarAssign(idnuse, rhs) => PVarAssign(go(idnuse), go(rhs))(p.pos)
        case p@PFieldAssign(fieldAcc, rhs) => PFieldAssign(go(fieldAcc), go(rhs))(p.pos)
        case p@PIf(keyword, cond, thn, elsKw, els) => PIf(go(keyword), go(cond), go(thn), elsKw map go, go(els))(p.pos)
        case p@PWhile(keyword, cond, invs, body) => PWhile(go(keyword), go(cond), invs map goPair, go(body))(p.pos)
        case p@PLocalVarDecl(keyword, idndef, typ, init) => PLocalVarDecl(go(keyword), go(idndef), go(typ), init map go)(p.pos)
        case p@PMethodCall(targets, method, args) => PMethodCall(targets map go, go(method), args map go)(p.pos)
        case p@PLabel(label, idndef, invs) => PLabel(go(label), go(idndef), invs map goPair)(p.pos)
        case p@PGoto(target) => PGoto(go(target))(p.pos)
        case p@PDefine(define, idndef, optArgs, exp) => PDefine(go(define), go(idndef), optArgs map (_ map go) , go(exp))(p.pos)
        case p@PLet(exp, nestedScope) => PLet(go(exp), go(nestedScope))(p.pos)
        case p@PLetNestedScope(idndef, body) => PLetNestedScope(go(idndef), go(body))(p.pos)
        case _: PSkip => parent

        case p@PProgram(files, macros, domains, fields, functions, predicates, methods, extensions, errors) => PProgram(files, macros map go, domains map go, fields map go, functions map go, predicates map go, methods map go, extensions map go, errors)(p.pos)
        case p@PLocalImport(imprt, file) => PLocalImport(go(imprt), file)(p.pos)
        case p@PStandardImport(imprt, file) => PStandardImport(go(imprt), file)(p.pos)
        case p@PMethod(idndef, formalArgs, formalReturns, pres, posts, body) => PMethod(go(idndef), formalArgs map go, formalReturns map go, pres map goPair, posts map goPair, body map go)(p.pos, p.annotations)
        case p@PDomain(idndef, typVars, funcs, axioms, interp) => PDomain(go(idndef), typVars map go, funcs map go, axioms map go, interp)(p.pos, p.annotations)
        case p@PField(field, idndef, typ) => PField(go(field), go(idndef), go(typ))(p.pos, p.annotations)
        case p@PFunction(idndef, formalArgs, typ, pres, posts, body) => PFunction(go(idndef), formalArgs map go, go(typ), pres map goPair, posts map goPair, body map go)(p.pos, p.annotations)
        case pdf@PDomainFunction(idndef, formalArgs, typ, unique, interp) => PDomainFunction(go(idndef), formalArgs map go, go(typ), unique, interp)(domainName = pdf.domainName)(pdf.pos, pdf.annotations)
        case p@PPredicate(predicate, idndef, formalArgs, body) => PPredicate(go(predicate), go(idndef), formalArgs map go, body map go)(p.pos, p.annotations)
        case pda@PAxiom(idndef, exp) => PAxiom(idndef map go, go(exp))(domainName = pda.domainName)(pda.pos, pda.annotations)
        case pe:PExtender => pe.transformExtension(this)
      }

      if (!allowChangingNodeType)
        assert(newNode.getClass == parent.getClass, "Transformer is not expected to change type of nodes.")

      newNode
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
