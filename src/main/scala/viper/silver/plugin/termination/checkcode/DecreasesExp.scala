package viper.silver.plugin.termination.checkcode

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives

sealed trait DecreasesExp extends ExtensionExp with Node

case class DecreasesTuple(extensionSubnodes: Seq[Exp] = Nil, pos: Position = NoPosition, errT: ErrorTrafo = NoTrafos) extends DecreasesExp {

  override def extensionIsPure = true

  override def typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */

  override def info: Info = NoInfo

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = text("decreases") <> parens(ssep(extensionSubnodes map (toParenDoc(_)), char(',') <> space))

  /**
    * Method that accesses all children of a node.
    * We allow 3 different types of children: Rewritable, Seq[Rewritable] and Option[Rewritable]
    * The supertype of all 3 is AnyRef
    *
    * @return Sequence of children
    */
  override def getChildren: Seq[Exp] = extensionSubnodes

  override def duplicate(children: Seq[AnyRef]): DecreasesTuple = {
    children match {
      case Seq(args: List[Exp]) => DecreasesTuple(args, pos, errT)
    }
  }
}

case class DecreasesStar(pos: Position = NoPosition, errT: ErrorTrafo = NoTrafos) extends DecreasesExp{
  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Nil

  override def typ: Type = Bool

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = text("decreasesStar")

  override def info: Info = NoInfo

}
