// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

object Transformer {
//   /* Attention: You most likely want to call initTree on the transformed node. */
//   def transform[A <: PNode](node: A,
//                             pre: PartialFunction[PNode, PNode] = PartialFunction.empty)(
//                              recursive: PNode => Boolean = !pre.isDefinedAt(_),
//                              post: PartialFunction[PNode, PNode] = PartialFunction.empty,
//                              allowChangingNodeType: Boolean = false,
//                              resultCheck: PartialFunction[(PNode, PNode), Unit] = PartialFunction.empty): A = {

//     @inline
//     def go[B <: PNode](root: B): B = {
//       transform(root, pre)(recursive, post, allowChangingNodeType, resultCheck)
//     }
//     @inline
//     def goPair[B <: PNode, C <: PNode](root: (B, C)): (B, C) = {
//       (go(root._1), go(root._2))
//     }

//     def recurse(parent: PNode): PNode = {
//       val newNode = parent match {
//         case _: PIdnDef => parent
//         case _: PIdnUse => parent
//         case _: PKeyword => parent
//         case _: POperator => parent
//         case p@PFormalArgDecl(idndef, typ) => PFormalArgDecl(go(idndef), go(typ))(p.pos)
//         case p@PFormalReturnDecl(idndef, typ) => PFormalReturnDecl(go(idndef), go(typ))(p.pos)
//         case p@PLogicalVarDecl(idndef, typ) => PLogicalVarDecl(go(idndef), go(typ))(p.pos)
//         case p@PLocalVarDecl(idndef, typ) => PLocalVarDecl(go(idndef), go(typ))(p.pos)
//         case p@PFieldDecl(idndef, typ) => PFieldDecl(go(idndef), go(typ))(p.pos)
//         case p@PTypeVarDecl(idndef) => PTypeVarDecl(go(idndef))(p.pos)
//         case p@PPrimitiv(keyword) => PPrimitiv(go(keyword))(p.pos)
//         case pdt@PDomainType(domain, args) =>
//           val newPdt = PDomainType(go(domain), args map go)(pdt.pos)
//           newPdt.kind = pdt.kind
//           newPdt
//         case p@PSeqType(seq, elementType) => PSeqType(go(seq), go(elementType))(p.pos)
//         case p@PSetType(set, elementType) => PSetType(go(set), go(elementType))(p.pos)
//         case p@PMultisetType(multiset, elementType) => PMultisetType(go(multiset), go(elementType))(p.pos)
//         case p@PMapType(map, keyType, valueType) => PMapType(map, go(keyType), go(valueType))(p.pos)
//         case _: PUnknown => parent
//         case _: PWandType => parent
//         case PFunctionType(argTypes, resultType) => PFunctionType(argTypes map go, go(resultType))
//         case p@PMagicWandExp(left, op, right) => PMagicWandExp(go(left), go(op), go(right))(p.pos)
//         case p@PBinExp(left, op, right) => PBinExp(go(left), go(op), go(right))(p.pos)
//         case p@PUnExp(op, exp) => PUnExp(go(op), go(exp))(p.pos)
//         case _: PIntLit => parent
//         case p@PResultLit(result) => PResultLit(go(result))(p.pos)
//         case p@PBoolLit(keyword, b) => PBoolLit(go(keyword), b)(p.pos)
//         case p@PNullLit(nul) => PNullLit(go(nul))(p.pos)
//         case p@PFieldAccess(rcv, dot, idnuse) => PFieldAccess(go(rcv), go(dot), go(idnuse))(p.pos)
//         case p@PCall(func, l, args, r, explicitType) =>
//           PCall(go(func), go(l), args map go, go(r), explicitType match {
//             case Some(t) => Some(go(t))
//             case None => None
//           })(p.pos)


//         case p@PUnfolding(unfolding, acc, in, exp) => PUnfolding(go(unfolding), go(acc), go(in), go(exp))(p.pos)
//         case p@PApplying(applying, wand, in, exp) => PApplying(go(applying), go(wand), go(in), go(exp))(p.pos)

//         case p@PExists(exists, vars, cs, triggers, exp) => PExists(go(exists), vars map go, go(cs), triggers map go, go(exp))(p.pos)
//         case p@PForall(forall, vars, cs, triggers, exp) => PForall(go(forall), vars map go, go(cs), triggers map go, go(exp))(p.pos)
//         case p@PTrigger(exp) => PTrigger(exp map go)(p.pos)
//         case p@PForPerm(forperm, vars, res, cs, exp) => PForPerm(go(forperm), vars map go, go(res), go(cs), go(exp))(p.pos)
//         case p@PCondExp(cond, q, thn, c, els) => PCondExp(go(cond), go(q), go(thn), go(c), go(els))(p.pos)
//         case p@PInhaleExhaleExp(l, in, c, ex, r) => PInhaleExhaleExp(go(l), go(in), go(c), go(ex), go(r))(p.pos)
//         case p@PCurPerm(k, l, loc, r) => PCurPerm(go(k), go(l), go(loc), go(r))(p.pos)
//         case _: PNoPerm => parent
//         case _: PFullPerm => parent
//         case _: PWildcard => parent
//         case _: PEpsilon => parent
//         case p@PAccPred(acc, loc, perm) => PAccPred(go(acc), go(loc), go(perm))(p.pos)
//         case p@POldExp(k, lbl, l, e, r) => POldExp(go(k), lbl map go, go(l), go(e), go(r))(p.pos)
//         case p@PEmptySeq(k, t, l, r) => PEmptySeq(go(k), go(t), go(l), go(r))(p.pos)
//         case p@PExplicitSeq(k, l, elems, r) => PExplicitSeq(go(k), go(l), elems map go, go(r))(p.pos)
//         case p@PRangeSeq(l, low, ds, high, r) => PRangeSeq(go(l), go(low), go(ds), go(high), go(r))(p.pos)
//         case p@PSeqSlice(seq, l, s, ds, e, r) => PSeqSlice(go(seq), go(l), s map go, go(ds), e map go, go(r))(p.pos)
//         case p@PSize(seq) => PSize(go(seq))(p.pos)
//         case p@PEmptySet(k, t, l, r) => PEmptySet(go(k), go(t), go(l), go(r))(p.pos)
//         case p@PLookup(seq, l, idx, r) => PLookup(go(seq), go(l), go(idx), go(r))(p.pos)
//         case p@PUpdate(seq, l, idx, a, elem, r) => PUpdate(go(seq), go(l), go(idx), go(a), go(elem), go(r))(p.pos)
//         case p@PExplicitSet(k, l, elems, r) => PExplicitSet(go(k), go(l), elems map go, go(r))(p.pos)
//         case p@PEmptyMultiset(k, t, l, r) => PEmptyMultiset(go(k), go(t), go(l), go(r))(p.pos)
//         case p@PExplicitMultiset(k, l, elems, r) => PExplicitMultiset(go(k), go(l), elems map go, go(r))(p.pos)

//         case p@PSeqn(ss) => PSeqn(ss map go)(p.pos)
//         case p@PFold(fold, e) => PFold(go(fold), go(e))(p.pos)
//         case p@PUnfold(unfold, e) => PUnfold(go(unfold), go(e))(p.pos)
//         case p@PPackageWand(pckg, e, proofScript) => PPackageWand(go(pckg), go(e), go(proofScript))(p.pos)
//         case p@PApplyWand(apply, e) => PApplyWand(go(apply), go(e))(p.pos)
//         case p@PExhale(exhale, e) => PExhale(go(exhale), go(e))(p.pos)
//         case p@PAssert(assert, e) => PAssert(go(assert), go(e))(p.pos)
//         case p@PAssume(assume, e) => PAssume(go(assume), go(e))(p.pos)
//         case p@PInhale(inhale, e) => PInhale(go(inhale), go(e))(p.pos)
//         case p@PQuasihavoc(quasihavoc, lhs, e) =>
//           PQuasihavoc(go(quasihavoc), lhs map goPair, go(e))(p.pos)
//         case p@PQuasihavocall(quasihavocall, vars, cc, lhs, e) =>
//           PQuasihavocall(go(quasihavocall), vars map go, go(cc), lhs map goPair, go(e))(p.pos)
//         case p@PEmptyMap(k, keyType, valueType, l, r) => PEmptyMap(go(k), go(keyType), go(valueType), go(l), go(r))(p.pos)
//         case p@PExplicitMap(k, l, exprs, r) => PExplicitMap(go(k), go(l), exprs map go, go(r))(p.pos)
//         case p@PMaplet(key, value) => PMaplet(go(key), go(value))(p.pos)
//         case p@PMapDomain(op, base) => PMapDomain(go(op), go(base))(p.pos)
//         case p@PMapRange(op, base) => PMapRange(go(op), go(base))(p.pos)
//         case p@PNewExp(k, fields) => PNewExp(go(k), fields map (_.map(go)))(p.pos)
//         case p@PAssign(targets, op, rhs) => PAssign(targets map go, op map go, go(rhs))(p.pos)
//         case p@PIf(keyword, cond, thn, elsKw, els) => PIf(go(keyword), go(cond), go(thn), elsKw map go, go(els))(p.pos)
//         case p@PWhile(keyword, cond, invs, body) => PWhile(go(keyword), go(cond), invs map goPair, go(body))(p.pos)
//         case p@PVars(keyword, vars, init) => PVars(go(keyword), vars map go, init map goPair)(p.pos)
//         case p@PLabel(label, idndef, invs) => PLabel(go(label), go(idndef), invs map goPair)(p.pos)
//         case p@PGoto(goto, target) => PGoto(go(goto), go(target))(p.pos)
//         case p@PDefine(anns, define, idndef, optArgs, exp) => PDefine(anns map go, go(define), go(idndef), optArgs map (_ map go) , go(exp))(p.pos)
//         case p@PLet(op, idndef, eq, exp, in, nestedScope) => PLet(go(op), go(idndef), go(eq), go(exp), go(in), go(nestedScope))(p.pos)
//         case p@PLetNestedScope(body) => PLetNestedScope(go(body))(p.pos)
//         case _: PSkip => parent

//         case p@PProgram(files, macros, domains, fields, functions, predicates, methods, extensions, errors) => PProgram(files, macros map go, domains map go, fields map go, functions map go, predicates map go, methods map go, extensions map go, errors)(p.pos)
//         case p@PImport(anns, imprt, local, file) => PImport(anns map go, go(imprt), local, go(file))(p.pos)
//         case p@PMethod(anns, k, idndef, formalArgs, returns, formalReturns, pres, posts, body) => PMethod(anns map go, go(k), go(idndef), formalArgs map go, returns map go, formalReturns map go, pres map goPair, posts map goPair, body map go)(p.pos)
//         case p@PDomain(anns, k, idndef, typVars, members, interp) => PDomain(anns map go, go(k), go(idndef), typVars map go, go(members), interp)(p.pos)
//         case p@PDomainMembers(funcs, axioms) => PDomainMembers(funcs map go, axioms map go)(p.pos)
//         case p@PFields(anns, k, fields) => PFields(anns map go, go(k), fields map go)(p.pos)
//         case p@PFunction(anns, k, idndef, formalArgs, typ, pres, posts, body) => PFunction(anns map go, go(k), go(idndef), formalArgs map go, go(typ), pres map goPair, posts map goPair, body map go)(p.pos)
//         case pdf@PDomainFunction(anns, unique, k, idndef, formalArgs, typ, interp) => PDomainFunction(anns map go, unique map go, go(k), go(idndef), formalArgs map go, go(typ), interp)(domainName = pdf.domainName)(pdf.pos)
//         case p@PPredicate(anns, k, idndef, formalArgs, body) => PPredicate(anns map go, go(k), go(idndef), formalArgs map go, body map go)(p.pos)
//         case pda@PAxiom(anns, k, idndef, exp) => PAxiom(anns map go, go(k), idndef map go, go(exp))(domainName = pda.domainName)(pda.pos)
//         case p@PBlock(inner) => PBlock(go(inner))(p.pos)
//         case pe:PExtender => pe.transformExtension(this)
//       }

//       if (!allowChangingNodeType)
//         assert(newNode.getClass == parent.getClass, "Transformer is not expected to change type of nodes.")

//       newNode
//     }



//     val beforeRecursion = pre.applyOrElse(node, identity[PNode])

//     resultCheck.applyOrElse((node, beforeRecursion), identity[(PNode, PNode)])

//     val afterRecursion = if (recursive(node)) {
//       recurse(beforeRecursion)
//     } else {
//       beforeRecursion
//     }
//     post.applyOrElse(afterRecursion, identity[PNode]).asInstanceOf[A]
//   }

  case class ParseTreeDuplicationError(original: PNode, newChildren: Seq[Any])
      extends RuntimeException(s"Cannot duplicate $original with new children $newChildren")
}
