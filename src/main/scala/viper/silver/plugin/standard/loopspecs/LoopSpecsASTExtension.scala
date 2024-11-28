package viper.silver.plugin.standard.loopspecs


import org.scalactic.PrettyMethods.Prettyizer
import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, text, toParenDoc}
import viper.silver.ast.utility.Consistency
import viper.silver.verifier.ConsistencyError


case class Old(exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends OldExp {
    override lazy val check : Seq[ConsistencyError] = Consistency.checkPure(exp)
}
case class PreExp{

}

case class LoopSpecs(
  cond: Exp,
  pres: Seq[Exp], 
  posts: Seq[Exp],
  body: Seqn,
  ghost: Option[Seqn],
  basecase: Option[Seqn])(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
    def extensionSubnodes: Seq[Node] = pres ++ posts ++ Seq(body) ++ ghost.map(seqn => seqn) ++ basecase.map(bc => bc)
    def prettyPrint: PrettyPrintPrimitives#Cont =  text("")
//        val preStr = pres.pretty
//        val postStr = posts.pretty
//        val ghostStr = ghost.map(_.pretty).getOrElse("")
//        val basecaseStr = basecase.map(_.pretty).getOrElse("")
//        s"${cond.pretty}\n$preStr\n$postStr\n${body.pretty}\n$ghostStr\n$basecaseStr"
    
    /** declarations contributed by this statement that should be added to the parent scope */
    override def declarationsInParentScope: Seq[Declaration] = Seq.empty
}

//object LoopSpecs {
//  val PredicateInstanceDomainName = "PredicateInstance"
//  def getType: Type = ???
//}
