package viper.silver.plugin.standard.loopspecs


import org.scalactic.PrettyMethods.Prettyizer
import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, parens, show, text, toParenDoc}
import viper.silver.ast.utility.Consistency
import viper.silver.verifier.{ConsistencyError, Success, VerificationResult}


case class PreExp(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp {

    // Like an old() expression it has a pure exp (no acc predicates...)
    override def extensionIsPure: Boolean = true

    override def extensionSubnodes: Seq[Node] = Seq(exp)

    override def typ: Type = exp.typ


    override def verifyExtExp(): VerificationResult = Success
    //Probably not called because all desugaring happens before verification

    /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
     * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
    override def prettyPrint: PrettyPrintPrimitives#Cont = text("pre") <> parens(show(exp))

    override lazy val check: Seq[ConsistencyError] = Consistency.checkPure(exp)
}


case class LoopSpecs(
  cond: Exp,
  pres: Exp,
  posts: Exp,
  body: Seqn,
  ghost: Option[Seqn],
  basecase: Option[Seqn])(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
    def extensionSubnodes: Seq[Node] = Seq(pres) ++ Seq(posts) ++ Seq(body) ++ ghost.map(seqn => seqn) ++ basecase.map(bc => bc)
    def prettyPrint: PrettyPrintPrimitives#Cont = text("LoopSpecs")
    // This should not be printed realistically. It should always be desugared. This is for debugging purposes.

    /** declarations contributed by this statement that should be added to the parent scope */
    override def declarationsInParentScope: Seq[Declaration] = Seq.empty
}