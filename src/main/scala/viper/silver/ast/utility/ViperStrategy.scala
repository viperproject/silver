/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast.utility

import viper.silver.ast._
import viper.silver.ast.utility.Rewriter._
import viper.silver.ast.utility.Rewriter.Traverse.Traverse
import viper.silver.verifier.errors.ErrorNode

/**
  * Viper specific Wrapper for the rewriting Strategies
  * Provides automatic back transformations for Node rewrites
  *
  * @param p Partial function to perform rewritings
  * @tparam C Type of context
  */
class ViperStrategy[C <: Context[Node]](p: PartialFunction[(Node, C), Node]) extends Strategy[Node, C](p) {
  override def preserveMetaData(old: Node, now: Node): Node = {
    ViperStrategy.preserveMetaData(old, now, this)
  }
}

/**
  * Viper specific Wrapper for Regex Strategies
  * Provides automatic back transformations for Node to Node rewrites
  *
  * @param a The automaton generated from the regular expression
  * @param p PartialFunction that describes rewriting
  * @param d Default context
  * @tparam C Type of context
  */
class ViperRegexStrategy[C](a: TRegexAutomaton, p: PartialFunction[(Node, RegexContext[Node, C]), Node], d: PartialContextR[Node, C]) extends RegexStrategy[Node, C](a, p, d) {

  override def preserveMetaData(old: Node, now: Node): Node = {
    ViperStrategy.preserveMetaData(old, now, this)
  }
}

class SlimViperRegexStrategy[C](a: TRegexAutomaton, p: PartialFunction[Node, Node]) extends SlimRegexStrategy[Node](a, p) {

  override def preserveMetaData(old: Node, now: Node): Node = {
    ViperStrategy.preserveMetaData(old, now, this)
  }
}


class ViperRegexBuilder[C](acc: (C, C) => C, comp: (C, C) => C, dflt: C) extends TreeRegexBuilder[Node, C](acc, comp, dflt) {

  /**
    * Generates a TreeRegexBuilderWithMatch by adding the matching part to the mix
    *
    * @param m Regular expression
    * @return TregexBuilderWithMatch that contains regex `f`
    */
  override def &>(m: Match): ViperRegexBuilderWithMatch[C] = new ViperRegexBuilderWithMatch[C](this, m)
}


class ViperRegexBuilderWithMatch[C](v: ViperRegexBuilder[C], m: Match) extends TreeRegexBuilderWithMatch[Node, C](v, m) {

  override def |->(p: PartialFunction[(Node, RegexContext[Node, C]), Node]): ViperRegexStrategy[C] = new ViperRegexStrategy[C](m.createAutomaton(), p, new PartialContextR[Node, C](v.default, v.accumulator, v.combinator))
}


class SlimViperRegexBuilder {

  def &>(m: Match) = new SlimViperRegexBuilderWithMatch(m)
}

class SlimViperRegexBuilderWithMatch(regex: Match) {

  def |->(p: PartialFunction[Node, Node]) = new SlimViperRegexStrategy[Node](regex.createAutomaton(), p)
}

/**
  * Factory for standard rewriting configurations
  */
object ViperStrategy {

  def SlimRegex(m: Match, p: PartialFunction[Node, Node]) = {
    new SlimViperRegexBuilder &> m |-> p
  }

  def Regex[C](m: Match, p: PartialFunction[(Node, RegexContext[Node, C]), Node], default: C, acc: (C, C) => C, comb: (C, C) => C) = {
    new ViperRegexBuilder[C](acc, comb, default) &> m |-> p
  }

  /**
    * Strategy without context
    *
    * @param p Partial function to perform rewriting
    * @param t Traversion mode
    * @return ViperStrategy
    */
  def Slim(p: PartialFunction[Node, Node], t: Traverse = Traverse.TopDown) = {
    new ViperStrategy[SimpleContext[Node]](new AddArtificialContext(p)) defaultContext new NoContext[Node] traverse t
  }

  /**
    * Strategy with context about ancestors and siblings
    *
    * @param p Partial function to perform rewriting
    * @param t Traversion mode
    * @return ViperStrategy
    */
  def Ancestor(p: PartialFunction[(Node, ContextA[Node]), Node], t: Traverse = Traverse.TopDown) = {
    new ViperStrategy[ContextA[Node]](p) defaultContext new PartialContextA[Node] traverse t
  }

  /**
    * Strategy with context about ancestors, siblings and custom context
    *
    * @param p          Partial function to perform rewriting
    * @param default    Default context
    * @param updateFunc Function that specifies how to update the custom context
    * @param t          Traversion mode
    * @tparam C Type of custom context
    * @return ViperStrategy
    */
  def Context[C](p: PartialFunction[(Node, ContextC[Node, C]), Node], default: C, updateFunc: PartialFunction[(Node, C), C] = PartialFunction.empty, t: Traverse = Traverse.TopDown) = {
    new ViperStrategy[ContextC[Node, C]](p) defaultContext new PartialContextC[Node, C](default, updateFunc) traverse t
  }

  /**
    * Function for automatic Error back transformation of nodes and conservation of metadata
    */
  def preserveMetaData(old: Node, now: Node, si: StrategyInterface[Node]): Node = {
    old match {
      case n: TransformableErrors =>
        val OldMetaData = old.getPrettyMetadata
        var NewMetaData = now.getPrettyMetadata

        if ((NewMetaData._1 == NoPosition) && (NewMetaData._2 == NoInfo) && (NewMetaData._3 == NoTrafos)) {
          NewMetaData = (OldMetaData._1, OldMetaData._2, OldMetaData._3)
        }

        // Only duplicate if old and new are actually different
        if (old ne now) {
          NewMetaData = (NewMetaData._1, NewMetaData._2, NewMetaData._3 + NodeTrafo(n.asInstanceOf[ErrorNode]))
          now.duplicateMeta(NewMetaData)
        } else {
          now
        }

      case _ => now
    }
  }


  /**
    * Duplicator for every interesting node of the viper AST
    *
    * @return Duplicated node
    */
  def viperDuplicator: PartialFunction[(Node, Seq[Any], (Position, Info, ErrorTrafo)), Node] = {
    case (il: IntLit, Seq(), meta) => IntLit(il.i)(meta._1, meta._2, meta._3)
    case (bl: BoolLit, Seq(), meta) => BoolLit(bl.value)(meta._1, meta._2, meta._3)
    case (nl: NullLit, _, meta) => NullLit()(meta._1, meta._2, meta._3)
    case (lv: LocalVar, _, meta) => LocalVar(lv.name)(lv.typ, meta._1, meta._2, meta._3)
    case (alv: AbstractLocalVar, _, meta) => alv
    // AS: added recursion on field: this was previously missing (as for all "shared" nodes in AST). But this could lead to the type of the field not being transformed consistently with its declaration (if the whole program is transformed)
    case (fa: FieldAccess, Seq(rcv: Exp, field: Field), meta) => FieldAccess(rcv, field)(meta._1, meta._2, meta._3)
    case (pa: PredicateAccess, Seq(params: Seq[Exp@unchecked]), meta) =>
      PredicateAccess(params, pa.predicateName)(meta._1, meta._2, meta._3)

    case (u: Unfolding, Seq(acc: PredicateAccessPredicate, e: Exp), meta) => Unfolding(acc, e)(meta._1, meta._2, meta._3)
    case (a: Applying, Seq(wand: MagicWand, e: Exp), meta) => Applying(wand, e)(meta._1, meta._2, meta._3)

    case (o: Old, Seq(e: Exp), meta) => Old(e)(meta._1, meta._2, meta._3)
    case (l: LabelledOld, Seq(e: Exp), meta) => LabelledOld(e, l.oldLabel)(meta._1, meta._2, meta._3)
    case (c: CondExp, Seq(cond: Exp, thn: Exp, els: Exp), meta) =>
      CondExp(cond, thn, els)(meta._1, meta._2, meta._3)
    case (l: Let, Seq(v: LocalVarDecl, exp1: Exp, body: Exp), meta) => Let(v, exp1, body)(meta._1, meta._2, meta._3)
    case (ex: Exists, Seq(v: Seq[LocalVarDecl@unchecked], e: Exp), meta) => Exists(v, e)(meta._1, meta._2, meta._3)
    case (f: Forall, Seq(v: Seq[LocalVarDecl@unchecked], triggers: Seq[Trigger@unchecked], e: Exp), meta) =>
      Forall(v, triggers, e)(meta._1, meta._2, meta._3)
    case (f: ForPerm, Seq(v: LocalVarDecl, fields: Seq[Location@unchecked], e: Exp), meta) =>
      ForPerm(v, fields, e)(meta._1, meta._2, meta._3)
    case (ie: InhaleExhaleExp, Seq(in: Exp, ex: Exp), meta) =>
      InhaleExhaleExp(in, ex)(meta._1, meta._2, meta._3)
    case (w: WildcardPerm, _, meta) => WildcardPerm()(meta._1, meta._2, meta._3)
    case (f: FullPerm, _, meta) => FullPerm()(meta._1, meta._2, meta._3)
    case (n: NoPerm, _, meta) => NoPerm()(meta._1, meta._2, meta._3)
    case (e: EpsilonPerm, _, meta) => EpsilonPerm()(meta._1, meta._2, meta._3)
    case (c: CurrentPerm, Seq(loc: LocationAccess), meta) => CurrentPerm(loc)(meta._1, meta._2, meta._3)
    case (f: FractionalPerm, Seq(left: Exp, right: Exp), meta) =>
      FractionalPerm(left, right)(meta._1, meta._2, meta._3)
    case (p: PermDiv, Seq(left: Exp, right: Exp), meta) =>
      PermDiv(left, right)(meta._1, meta._2, meta._3)
    case (f: FieldAccessPredicate, Seq(loc: FieldAccess, perm: Exp), meta) =>
      FieldAccessPredicate(loc, perm)(meta._1, meta._2, meta._3)
    case (p: PredicateAccessPredicate, Seq(loc: PredicateAccess, perm: Exp), meta) =>
      PredicateAccessPredicate(loc, perm)(meta._1, meta._2, meta._3)
    case (fa: FuncApp, Seq(args: Seq[Exp@unchecked]), meta) =>
      FuncApp(fa.funcname, args)(meta._1, meta._2, fa.typ, fa.formalArgs, meta._3)
    case (df: DomainFuncApp, Seq(args: Seq[Exp@unchecked]), meta) =>
      DomainFuncApp(df.funcname, args, df.typVarMap)(meta._1, meta._2, df.typ, df.formalArgs, df.domainName, meta._3)

    case (m: Minus, Seq(e: Exp), meta) => Minus(e)(meta._1, meta._2, meta._3)
    case (n: Not, Seq(e: Exp), meta) => Not(e)(meta._1, meta._2, meta._3)

    case (o: Or, Seq(l: Exp, r: Exp), meta) => Or(l, r)(meta._1, meta._2, meta._3)
    case (a: And, Seq(l: Exp, r: Exp), meta) => And(l, r)(meta._1, meta._2, meta._3)
    case (i: Implies, Seq(l: Exp, r: Exp), meta) => Implies(l, r)(meta._1, meta._2, meta._3)
    case (m: MagicWand, Seq(l: Exp, r: Exp), meta) => MagicWand(l, r)(meta._1, meta._2, meta._3)

    case (a: Add, Seq(l: Exp, r: Exp), meta) => Add(l, r)(meta._1, meta._2, meta._3)
    case (s: Sub, Seq(l: Exp, r: Exp), meta) => Sub(l, r)(meta._1, meta._2, meta._3)
    case (m: Mul, Seq(l: Exp, r: Exp), meta) => Mul(l, r)(meta._1, meta._2, meta._3)
    case (d: Div, Seq(l: Exp, r: Exp), meta) => Div(l, r)(meta._1, meta._2, meta._3)
    case (m: Mod, Seq(l: Exp, r: Exp), meta) => Mod(l, r)(meta._1, meta._2, meta._3)

    case (lc: LtCmp, Seq(l: Exp, r: Exp), meta) => LtCmp(l, r)(meta._1, meta._2, meta._3)
    case (le: LeCmp, Seq(l: Exp, r: Exp), meta) => LeCmp(l, r)(meta._1, meta._2, meta._3)
    case (gt: GtCmp, Seq(l: Exp, r: Exp), meta) => GtCmp(l, r)(meta._1, meta._2, meta._3)
    case (ge: GeCmp, Seq(l: Exp, r: Exp), meta) => GeCmp(l, r)(meta._1, meta._2, meta._3)

    case (eq: EqCmp, Seq(l: Exp, r: Exp), meta) => EqCmp(l, r)(meta._1, meta._2, meta._3)
    case (neq: NeCmp, Seq(l: Exp, r: Exp), meta) => NeCmp(l, r)(meta._1, meta._2, meta._3)

    case (pm: PermMinus, Seq(e: Exp), meta) => PermMinus(e)(meta._1, meta._2, meta._3)
    case (pa: PermAdd, Seq(l: Exp, r: Exp), meta) => PermAdd(l, r)(meta._1, meta._2, meta._3)
    case (ps: PermSub, Seq(l: Exp, r: Exp), meta) => PermSub(l, r)(meta._1, meta._2, meta._3)
    case (pm: PermMul, Seq(l: Exp, r: Exp), meta) => PermMul(l, r)(meta._1, meta._2, meta._3)
    case (ip: IntPermMul, Seq(l: Exp, r: Exp), meta) => IntPermMul(l, r)(meta._1, meta._2, meta._3)

    case (pc: PermLtCmp, Seq(l: Exp, r: Exp), meta) => PermLtCmp(l, r)(meta._1, meta._2, meta._3)
    case (pc: PermLeCmp, Seq(l: Exp, r: Exp), meta) => PermLeCmp(l, r)(meta._1, meta._2, meta._3)
    case (pc: PermGtCmp, Seq(l: Exp, r: Exp), meta) => PermGtCmp(l, r)(meta._1, meta._2, meta._3)
    case (pc: PermGeCmp, Seq(l: Exp, r: Exp), meta) => PermGeCmp(l, r)(meta._1, meta._2, meta._3)

    case (es: EmptySeq, Seq(elemTyp: Type), meta) => EmptySeq(elemTyp)(meta._1, meta._2, meta._3)
    case (es: ExplicitSeq, Seq(elems: Seq[Exp@unchecked]), meta) => ExplicitSeq(elems)(meta._1, meta._2, meta._3)
    case (rs: RangeSeq, Seq(low: Exp, high: Exp), meta) => RangeSeq(low, high)(meta._1, meta._2, meta._3)
    case (sa: SeqAppend, Seq(left: Exp, right: Exp), meta) => SeqAppend(left, right)(meta._1, meta._2, meta._3)
    case (si: SeqIndex, Seq(seq: Exp, idx: Exp), meta) => SeqIndex(seq, idx)(meta._1, meta._2, meta._3)
    case (st: SeqTake, Seq(seq: Exp, n: Exp), meta) => SeqTake(seq, n)(meta._1, meta._2, meta._3)
    case (sd: SeqDrop, Seq(seq: Exp, n: Exp), meta) => SeqDrop(seq, n)(meta._1, meta._2, meta._3)
    case (sc: SeqContains, Seq(elem: Exp, seq: Exp), meta) => SeqContains(elem, seq)(meta._1, meta._2, meta._3)
    case (su: SeqUpdate, Seq(seq: Exp, idx: Exp, elem: Exp), meta) =>
      SeqUpdate(seq, idx, elem)(meta._1, meta._2, meta._3)
    case (sl: SeqLength, Seq(seq: Exp), meta) => SeqLength(seq)(meta._1, meta._2, meta._3)

    case (e: EmptySet, Seq(elemTyp: Type), meta) => EmptySet(elemTyp)(meta._1, meta._2, meta._3)
    case (e: ExplicitSet, Seq(elems: Seq[Exp@unchecked]), meta) => ExplicitSet(elems)(meta._1, meta._2, meta._3)
    case (e: EmptyMultiset, Seq(elemTyp: Type), meta) => EmptyMultiset(elemTyp)(meta._1, meta._2, meta._3)
    case (e: ExplicitMultiset, Seq(elems: Seq[Exp@unchecked]), meta) => ExplicitMultiset(elems)(meta._1, meta._2, meta._3)
    case (a: AnySetUnion, Seq(left: Exp, right: Exp), meta) => AnySetUnion(left, right)(meta._1, meta._2, meta._3)
    case (a: AnySetIntersection, Seq(left: Exp, right: Exp), meta) => AnySetIntersection(left, right)(meta._1, meta._2, meta._3)
    case (a: AnySetSubset, Seq(left: Exp, right: Exp), meta) => AnySetSubset(left, right)(meta._1, meta._2, meta._3)
    case (a: AnySetMinus, Seq(left: Exp, right: Exp), meta) => AnySetMinus(left, right)(meta._1, meta._2, meta._3)
    case (a: AnySetContains, Seq(elem: Exp, s: Exp), meta) => AnySetContains(elem, s)(meta._1, meta._2, meta._3)
    case (a: AnySetCardinality, Seq(s: Exp), meta) => AnySetCardinality(s)(meta._1, meta._2, meta._3)

    case (p: Program, Seq(domains: Seq[Domain@unchecked], fields: Seq[Field@unchecked], functions: Seq[Function@unchecked], predicates: Seq[Predicate@unchecked], methods: Seq[Method@unchecked]), meta) =>
      Program(domains, fields, functions, predicates, methods)(meta._1, meta._2, meta._3)


    case (d: Domain, Seq(functions: Seq[DomainFunc@unchecked], axioms: Seq[DomainAxiom@unchecked], typeVariables: Seq[TypeVar@unchecked]), meta) =>
      Domain(d.name, functions, axioms, typeVariables)(meta._1, meta._2, meta._3)

    case (f: Field, Seq(singleType: Type), meta) =>
      Field(f.name, singleType)(meta._1, meta._2, meta._3)

    case (f: Function, Seq(parameters: Seq[LocalVarDecl@unchecked], aType: Type, preconditions: Seq[Exp@unchecked], postconditions: Seq[Exp@unchecked], decreases: Option[DecClause@unchecked], body: Option[Exp@unchecked]), meta) =>
      Function(f.name, parameters, aType, preconditions, postconditions, decreases, body)(meta._1, meta._2, meta._3)

    case (p: Predicate, Seq(parameters: Seq[LocalVarDecl@unchecked], body: Option[Exp@unchecked]), meta) =>
      Predicate(p.name, parameters, body)(meta._1, meta._2, meta._3)

    case (m: Method, Seq(parameters: Seq[LocalVarDecl@unchecked], results: Seq[LocalVarDecl@unchecked], preconditions: Seq[Exp@unchecked], postconditions: Seq[Exp@unchecked], body: Option[Seqn@unchecked]), meta) =>
      Method(m.name, parameters, results, preconditions, postconditions, body)(meta._1, meta._2, meta._3)

    case (da: DomainAxiom, Seq(body: Exp), meta) =>
      DomainAxiom(da.name, body)(meta._1, meta._2, da.domainName, meta._3)

    case (df: DomainFunc, Seq(parameters: Seq[LocalVarDecl@unchecked], aType: Type), meta) =>
      DomainFunc(df.name, parameters, aType, df.unique)(meta._1, meta._2, df.domainName, meta._3)

    case (Bool, _, meta) => Bool

    case (dt: DomainType, Seq(domainName: Domain, typeVariables: Map[TypeVar@unchecked, Type@unchecked]), meta) =>
      DomainType(domainName, typeVariables)

    case (Int, _, meta) => Int
    case (Perm, _, meta) => Perm
    case (InternalType, _, meta) => InternalType
    case (Wand, _, meta) => Wand
    case (Ref, _, meta) => Ref
    case (st: SeqType, Seq(elementType: Type), meta) => SeqType(elementType)
    case (st: SetType, Seq(elementType: Type), meta) => SetType(elementType)
    case (mt: MultisetType, Seq(elementType: Type), meta) => MultisetType(elementType)
    case (t: TypeVar, _, meta) => t

    case (ld: LocalVarDecl, Seq(singleType: Type), meta) =>
      LocalVarDecl(ld.name, singleType)(meta._1, meta._2, meta._3)

    case (a: Assert, Seq(expression: Exp), meta) =>
      Assert(expression)(meta._1, meta._2, meta._3)

    case (e: Exhale, Seq(expression: Exp), meta) =>
      Exhale(expression)(meta._1, meta._2, meta._3)

    case (fa: FieldAssign, Seq(field: FieldAccess, value: Exp), meta) =>
      FieldAssign(field, value)(meta._1, meta._2, meta._3)

    case (f: Fold, Seq(accessPredicate: PredicateAccessPredicate), meta) =>
      Fold(accessPredicate)(meta._1, meta._2, meta._3)

    case (f: Fresh, Seq(variables: Seq[LocalVar@unchecked]), meta) =>
      Fresh(variables)(meta._1, meta._2, meta._3)

    case (c: Constraining, Seq(variables: Seq[LocalVar@unchecked], body: Seqn), meta) =>
      Constraining(variables, body)(meta._1, meta._2, meta._3)

    // We dont recurse on goto
    case (g: Goto, _, meta) => Goto(g.target)(meta._1, meta._2, meta._3)

    case (i: If, Seq(condition: Exp, ifTrue: Seqn, ifFalse: Seqn), meta) =>
      If(condition, ifTrue, ifFalse)(meta._1, meta._2, meta._3)

    case (i: Inhale, Seq(expression: Exp), meta) =>
      Inhale(expression)(meta._1, meta._2, meta._3)

    case (l: Label, invars: Seq[Exp@unchecked], meta) => Label(l.name, invars)(meta._1, meta._2, meta._3)

    case (l: LocalVarAssign, Seq(variable: LocalVar, value: Exp), meta) =>
      LocalVarAssign(variable, value)(meta._1, meta._2, meta._3)

    case (m: MethodCall, Seq(arguments: Seq[Exp@unchecked], variables: Seq[LocalVar@unchecked]), meta) =>
      MethodCall(m.methodName, arguments, variables)(meta._1, meta._2, meta._3)

    case (n: NewStmt, Seq(target: LocalVar, fields: Seq[Field@unchecked]), meta) =>
      NewStmt(target, fields)(meta._1, meta._2, meta._3)

    case (s: Seqn, Seq(x: Seq[Stmt@unchecked], locals: Seq[LocalVarDecl@unchecked]), meta) =>
      Seqn(x, locals)(meta._1, meta._2, meta._3)

    case (u: Unfold, Seq(predicate: PredicateAccessPredicate), meta) =>
      Unfold(predicate)(meta._1, meta._2, meta._3)

    case (p: Package, Seq(wand: MagicWand, proofScript: Seqn), meta) =>
      Package(wand, proofScript)(meta._1, meta._2, meta._3)

    case (a: Apply, Seq(wand: MagicWand), meta) =>
      Apply(wand)(meta._1, meta._2, meta._3)

    case (w: While, Seq(condition: Exp, invariants: Seq[Exp@unchecked], body: Seqn), meta) =>
      While(condition, invariants, body)(meta._1, meta._2, meta._3)

    case (t: Trigger, Seq(expressions: Seq[Exp@unchecked]), meta) =>
      Trigger(expressions)(meta._1, meta._2, meta._3)

    case (n, args, meta) =>
      throw new Exception("node: " + n + " with args: " + args + " and meta info: " + meta + " does not match anything inside the viper duplicator")
  }

}
