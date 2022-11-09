package viper.silver.plugin.standard.reasoning

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, group, nil, show, showType, showVars, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives

/** An `FailureExpectedInfo` info that tells us that this assert is a existential elimination. */
case object ReasoningInfo extends FailureExpectedInfo

//version with Local var decl
case class ExistentialElim(varList: Seq[LocalVarDecl], trigs: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {

// version without local var decl (not used even in version without local vars in PAST)
//case class ExistentialElim(varList: Seq[(String, Type)], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    //version with local var decl
    text("obtain") <+> showVars(varList) <+>
    text("where") <+> (if (trigs.isEmpty) nil else space <> ssep(trigs map show, space)) <+>
    toParenDoc(exp)

    // version without local var decl (not used even in version without local vars in PAST)
    //text("obtain") <+> text("(") <+> ssep(varList.map { case (id,typ) => text(id) <+> ":" <+> showType(typ)}, group(char (','))) <+> text(")") <+>
    //text("where") <+> toParenDoc(exp)
  }

  // version with local var decl
  //override val extensionSubnodes: Seq[Node] = varList ++ Seq(exp)

  // version without local var decl
  override val extensionSubnodes: Seq[Node] = Seq(exp)

}
/*
case class ExistentialElim(vardecl:Arg, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("obtain") <+> showVars(Seq(vardecl))
    text("where") <+> toParenDoc(exp)
  }

  override val extensionSubnodes: Seq[Node] = Seq(exp)
}
*/