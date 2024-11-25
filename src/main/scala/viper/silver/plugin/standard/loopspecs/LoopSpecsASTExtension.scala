package viper.silver.plugin.standard.loopspecs


import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives

case class LoopSpecs(
  //keyword: While.type,
  cond: Exp,
  pres: Seq[Exp], 
  posts: Seq[Exp],
  body: Seqn,
  ghost: Option[Seqn],
  basecase: Option[Seqn])(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
    def extensionSubnodes: Seq[Node]
    def prettyPrint: PrettyPrintPrimitives#Cont
    
    /** declarations contributed by this statement that should be added to the parent scope */
    def declarationsInParentScope: Seq[Declaration] = Seq.empty
}

object LoopSpecs {
  val PredicateInstanceDomainName = "PredicateInstance"
  def getType: Type = ???
}
