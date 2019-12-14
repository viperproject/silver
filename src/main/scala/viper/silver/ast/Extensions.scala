package viper.silver.ast

import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, show, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.verifier.{ConsistencyError, VerificationResult}

import scala.None


case object PredicateInstanceType extends ExtensionType {

  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = typVarsMap.getOrElse(this.typeVariables.head, this)
  override def isConcrete: Boolean = true
}


case class PredicateInstance(p: String, args: Seq[Exp])
                            (override val pos: Position = NoPosition,
                             override val info: Info = NoInfo,
                             override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = args

  override def typ: Type = PredicateInstanceType

  override def verifyExtExp(): VerificationResult = ???

  override def prettyPrint: PrettyPrintPrimitives#Cont =
    text("PredicateInstance") <> parens(text(p) <> parens(ssep(args map show, char (',') <> space)))

  lazy val predicateAccessPredicate: PredicateAccessPredicate = PredicateAccessPredicate(PredicateAccess(args, p)(), EpsilonPerm()())()
}

case class NestedPredicates(p1: Exp, p2: Exp)
                           (override val pos: Position = NoPosition,
                            override val info: Info = NoInfo,
                            override val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {
  override def typ: Type = Bool

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq(p1, p2)

  override def verifyExtExp(): VerificationResult = ???

  override lazy val check: Seq[ConsistencyError] = Nil ++
    (if (p1.typ.isSubtype(PredicateInstanceType)) {None}
    else {Some(ConsistencyError("Expected Predicate Instance Type. But is " + p1.typ, p1.pos))}) ++
    (if (p2.typ.isSubtype(PredicateInstanceType)) {None}
    else {Some(ConsistencyError("Expected Predicate Instance Type. But is " + p2.typ, p2.pos))})

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont =
    text("NestedPredicate") <> parens(ssep(Seq(p1, p2) map show, char (',') <> space))
}