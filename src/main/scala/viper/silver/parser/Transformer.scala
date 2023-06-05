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
        case _: PIdnDef => parent
        case _: PIdnUse => parent
        case p@PFormalArgDecl(idndef, typ) => PFormalArgDecl(go(idndef), go(typ))(p.pos)
        case p@PFormalReturnDecl(idndef, typ) => PFormalReturnDecl(go(idndef), go(typ))(p.pos)
        case p@PLogicalVarDecl(idndef, typ) => PLogicalVarDecl(go(idndef), go(typ))(p.pos)
        case p@PLocalVarDecl(idndef, typ) => PLocalVarDecl(go(idndef), go(typ))(p.pos)
        case p@PFieldDecl(idndef, typ) => PFieldDecl(go(idndef), go(typ))(p.pos)
        case p@PTypeVarDecl(idndef) => PTypeVarDecl(go(idndef))(p.pos)
        case _: PPrimitiv => parent
        case pdt@PDomainType(domain, args) =>
          val newPdt = PDomainType(go(domain), args map go)(pdt.pos)
          newPdt.kind = pdt.kind
          newPdt
        case p@PSeqType(elementType) => PSeqType(go(elementType))(p.pos)
        case p@PSetType(elementType) => PSetType(go(elementType))(p.pos)
        case p@PMultisetType(elementType) => PMultisetType(go(elementType))(p.pos)
          /* Maps:
        case PSeqType(elementType) => PSeqType(go(elementType))
        case PSetType(elementType) => PSetType(go(elementType))
        case PMultisetType(elementType) => PMultisetType(go(elementType))
           */
        case p@PMapType(keyType, valueType) => PMapType(go(keyType), go(valueType))(p.pos)
        case _: PUnknown => parent
        case _: PPredicateType | _: PWandType => parent
        case PFunctionType(argTypes, resultType) => PFunctionType(argTypes map go, go(resultType))
        case p@PMagicWandExp(left, right) => PMagicWandExp(go(left), go(right))(p.pos)
        case p@PBinExp(left, op, right) => PBinExp(go(left), op, go(right))(p.pos)
        case p@PUnExp(op, exp) => PUnExp(op, go(exp))(p.pos)
        case _: PIntLit => parent
        case _: PResultLit => parent
        case _: PBoolLit => parent
        case _: PNullLit => parent
        case p@PFieldAccess(rcv, idnuse) => PFieldAccess(go(rcv), go(idnuse))(p.pos)
        case p@PCall(func, args, explicitType) =>
          PCall(go(func), args map go, explicitType match {
            case Some(t) => Some(go(t))
            case None => None
          })(p.pos)


        case p@PUnfolding(acc, exp) => PUnfolding(go(acc), go(exp))(p.pos)
        case p@PApplying(wand, exp) => PApplying(go(wand), go(exp))(p.pos)

        case p@PExists(vars, triggers, exp) => PExists(vars map go, triggers map go, go(exp))(p.pos)
        case p@PForall(vars, triggers, exp) => PForall(vars map go, triggers map go, go(exp))(p.pos)
        case p@PTrigger(exp) => PTrigger(exp map go)(p.pos)
        case p@PForPerm(vars, res, exp) => PForPerm(vars map go, go(res), go(exp))(p.pos)
        case p@PCondExp(cond, thn, els) => PCondExp(go(cond), go(thn), go(els))(p.pos)
        case p@PInhaleExhaleExp(in, ex) => PInhaleExhaleExp(go(in), go(ex))(p.pos)
        case p@PCurPerm(loc) => PCurPerm(go(loc))(p.pos)
        case _: PNoPerm => parent
        case _: PFullPerm => parent
        case _: PWildcard => parent
        case _: PEpsilon => parent
        case p@PAccPred(loc, perm) => PAccPred(go(loc), go(perm))(p.pos)
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
          // MAPS:
        //case PAccPred(loc, perm) => PAccPred(go(loc), go(perm))
        //case POld(e) => POld(go(e))
        //case PLabelledOld(lbl, e) => PLabelledOld(go(lbl), go(e))
        //case PEmptySeq(t) => PEmptySeq(go(t))
        //case PExplicitSeq(elems) => PExplicitSeq(elems map go)
        //case PRangeSeq(low, high) => PRangeSeq(go(low), go(high))
        case p@PLookup(seq, idx) => PLookup(go(seq), go(idx))(p.pos)
        //case PSeqTake(seq, n) => PSeqTake(go(seq), go(n))
        //case PSeqDrop(seq, n) => PSeqDrop(go(seq), go(n))
        case p@PUpdate(seq, idx, elem) => PUpdate(go(seq), go(idx), go(elem))(p.pos)
        //case PSize(seq) => PSize(go(seq))
        //case PEmptySet(t) => PEmptySet(go(t))
        //        case _: PEmptySet => parent
        case p@PExplicitSet(elems) => PExplicitSet(elems map go)(p.pos)
        case p@PEmptyMultiset(t) => PEmptyMultiset(go(t))(p.pos)
        //        case _: PEmptyMultiset => parent
        case p@PExplicitMultiset(elems) => PExplicitMultiset(elems map go)(p.pos)

        case p@PSeqn(ss) => PSeqn(ss map go)(p.pos)
        case p@PFold(e) => PFold(go(e))(p.pos)
        case p@PUnfold(e) => PUnfold(go(e))(p.pos)
        case p@PPackageWand(e, proofScript) => PPackageWand(go(e), go(proofScript))(p.pos)
        case p@PApplyWand(e) => PApplyWand(go(e))(p.pos)
        case p@PExhale(e) => PExhale(go(e))(p.pos)
        case p@PAssert(e) => PAssert(go(e))(p.pos)
        case p@PAssume(e) => PAssume(go(e))(p.pos)
        case p@PInhale(e) => PInhale(go(e))(p.pos)
        case p@PQuasihavoc(lhs, e) => PQuasihavoc(lhs map go, go(e))(p.pos)
        case p@PQuasihavocall(vars, lhs, e) => PQuasihavocall(vars map go, lhs map go, go(e))(p.pos)
          // MAPS:
        //case PExplicitMultiset(elems) => PExplicitMultiset(elems map go)
        case p@PEmptyMap(keyType, valueType) => PEmptyMap(go(keyType), go(valueType))(p.pos)
        case p@PExplicitMap(exprs) => PExplicitMap(exprs map go)(p.pos)
        case p@PMaplet(key, value) => PMaplet(go(key), go(value))(p.pos)
        case p@PMapDomain(base) => PMapDomain(go(base))(p.pos)
        case p@PMapRange(base) => PMapRange(go(base))(p.pos)
        //case PSeqn(ss) => PSeqn(ss map go)
        //case PFold(e) => PFold(go(e))
        //case PUnfold(e) => PUnfold(go(e))
        //case PPackageWand(e, proofScript) => PPackageWand(go(e), go(proofScript))
        //case PApplyWand(e) => PApplyWand(go(e))
        //case PExhale(e) => PExhale(go(e))
        //case PAssert(e) => PAssert(go(e))
        //case PAssume(e) => PAssume(go(e))
        //case PInhale(e) => PInhale(go(e))
        case p@PNewExp(fields) => PNewExp(fields map (_.map(go)))(p.pos)
        case p@PAssign(targets, rhs) => PAssign(targets map go, go(rhs))(p.pos)
        case p@PIf(cond, thn, els) => PIf(go(cond), go(thn), go(els))(p.pos)
        case p@PWhile(cond, invs, body) => PWhile(go(cond), invs map go, go(body))(p.pos)
        case p@PVars(vars, init) => PVars(vars map go, init map go)(p.pos)
        case p@PLabel(idndef, invs) => PLabel(go(idndef), invs map go)(p.pos)
        case p@PGoto(target) => PGoto(go(target))(p.pos)
        case p@PDefine(idndef, optArgs, exp) => PDefine(go(idndef), optArgs map (_ map go) , go(exp))(p.pos)
        case p@PLet(exp, nestedScope) => PLet(go(exp), go(nestedScope))(p.pos)
        case p@PLetNestedScope(idndef, body) => PLetNestedScope(go(idndef), go(body))(p.pos)
        case _: PSkip => parent

        case p@PProgram(files, macros, domains, fields, functions, predicates, methods, extensions, errors) => PProgram(files, macros map go, domains map go, fields map go, functions map go, predicates map go, methods map go, extensions map go, errors)(p.pos)
        case p@PLocalImport(file) => PLocalImport(file)(p.pos)
        case p@PStandardImport(file) => PStandardImport(file)(p.pos)
        case p@PMethod(idndef, formalArgs, formalReturns, pres, posts, body) => PMethod(go(idndef), formalArgs map go, formalReturns map go, pres map go, posts map go, body map go)(p.pos, p.annotations)
        case p@PDomain(idndef, typVars, funcs, axioms, interp) => PDomain(go(idndef), typVars map go, funcs map go, axioms map go, interp)(p.pos, p.annotations)
        case p@PFields(fields) => PFields(fields map go)(p.pos, p.annotations)
        case p@PFunction(idndef, formalArgs, typ, pres, posts, body) => PFunction(go(idndef), formalArgs map go, go(typ), pres map go, posts map go, body map go)(p.pos, p.annotations)
        case pdf@PDomainFunction(idndef, formalArgs, typ, unique, interp) => PDomainFunction(go(idndef), formalArgs map go, go(typ), unique, interp)(domainName = pdf.domainName)(pdf.pos, pdf.annotations)
        case p@PPredicate(idndef, formalArgs, body) => PPredicate(go(idndef), formalArgs map go, body map go)(p.pos, p.annotations)
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
