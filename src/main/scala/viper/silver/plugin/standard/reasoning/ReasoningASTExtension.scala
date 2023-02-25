package viper.silver.plugin.standard.reasoning

import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, braces, brackets, char, defaultIndent, group, line, lineIfSomeNonEmpty, nest, nil, parens, show, showBlock, showContracts, showStmt, showVars, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.{Consistency, Expressions}
import viper.silver.plugin.standard.termination.PDecreasesClause
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}


/** An `FailureExpectedInfo` info that tells us that this assert is a existential elimination. */
case object ReasoningInfo extends FailureExpectedInfo

case class ExistentialElim(varList: Seq[LocalVarDecl], trigs: Seq[Trigger], exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt {
  override lazy val check: Seq[ConsistencyError] = Consistency.checkPure(exp) ++
    (if (!(exp isSubtype Bool)) Seq(ConsistencyError(s"Body of existential quantifier must be of Bool type, but found ${exp.typ}", exp.pos)) else Seq()) ++
    (if (varList.isEmpty) Seq(ConsistencyError("Quantifier must have at least one quantified variable.", pos)) else Seq())

  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("obtain") <+> showVars(varList) <+>
      text("where") <+> (if (trigs.isEmpty) nil else space <> ssep(trigs map show, space)) <+>
      toParenDoc(exp)
  }

  override val extensionSubnodes: Seq[Node] = varList ++ trigs ++ Seq(exp)


  /** declarations contributed by this statement that should be added to the parent scope */
  override def declarationsInParentScope: Seq[Declaration] = varList


}

case class UniversalIntro(varList: Seq[LocalVarDecl], triggers: Seq[Trigger], exp1: Exp, exp2: Exp, block: Seqn)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt with Scope {
  // See also Expression Line 566
  override lazy val check: Seq[ConsistencyError] =
    (if (!(exp1 isSubtype Bool)) Seq(ConsistencyError(s"Body of universal quantifier must be of Bool type, but found ${exp1.typ}", exp1.pos)) else Seq()) ++
    (if (varList.isEmpty) Seq(ConsistencyError("Quantifier must have at least one quantified variable.", pos)) else Seq()) ++
    Consistency.checkAllVarsMentionedInTriggers(varList, triggers)


  override val scopedDecls = varList


  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    text("prove forall") <+> showVars(varList) <+>
      text("assuming") <+>
      toParenDoc(exp1) <+>
      text("implies") <+> toParenDoc(exp2) <+>
      showBlock(block)
  }

  override val extensionSubnodes: Seq[Node] = varList ++ triggers ++ Seq(exp1) ++ Seq(exp2) ++ Seq(block)
}

sealed trait FlowVar extends Node {

}

case class Heap()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowVar {

}

case class Var(decl:Exp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowVar {
  def var_decl: Exp = decl
}
case class FlowAnnotation(v: FlowVar, varList: Seq[FlowVar])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with Node with Scope {
//sealed trait FlowAnnotation extends ExtensionExp with Node with Scope {
   override def extensionIsPure: Boolean = true

  override val scopedDecls = Seq()

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "FlowAnalysis: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("FlowAnalysis: verifyExtExp has not been implemented.", pos)))

  }

  override def extensionSubnodes: Seq[Node] = {
    if (v.isInstanceOf[Var]) (Seq(v.asInstanceOf[Var].var_decl)) else (Seq()) ++ varList.filter(vl => vl.isInstanceOf[Var]).map(vl => vl.asInstanceOf[Var].var_decl)
  }

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced") <+> (v match {
      case value: Var => (show(value.var_decl))
      case _ => text("heap")
    })  <+>
      text("by") <+>
      ssep(varList.map {
        case value: Var => show(value.var_decl)
        case _ => text("heap")
      }, group(char(',') <> line(" ")))
  }
}

/*
case class FlowAnnotationVar(v: Exp, varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = Seq(v) ++ varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced") <+> show(v) <+>
    text("by") <+>
      ssep(varList map show, group(char (',') <> line(" ")))
  }
}

case class FlowAnnotationVarHeapArg(v: Exp, varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = Seq(v) ++ varList
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced") <+> show(v) <+>
      text("by") <+>
      ssep(varList map show, group(char(',') <> line(" "))) <+> text(", heap")
  }
}

case class FlowAnnotationHeap(varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced heap") <+>
      text("by") <+>
      ssep(varList map show, group(char (',') <> line(" ")))
  }
}

case class FlowAnnotationHeapHeapArg(varList: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends FlowAnnotation {

  override def extensionSubnodes: Seq[Node] = varList

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("influenced heap") <+>
      text("by") <+>
      ssep(varList map show, group(char (',') <> line(" "))) <+> text(", heap")

  }
}

 */

case class Lemma()(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with Node with Scope {

  override def extensionIsPure: Boolean = true

  override val scopedDecls = Seq()

  override def typ: Type = Bool

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "Lemma: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("Lemma: verifyExtExp has not been implemented.", pos)))
  }

  override def extensionSubnodes: Seq[Node] = Seq()

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("isLemma")

  }

  /*
  override def extensionSubnodes: Seq[Node] = method.subnodes

  override lazy val check: Seq[ConsistencyError] = {

    var errors: Seq[ConsistencyError] = Seq()

    var decreasesclauses = method.posts.filter(post => post.isInstanceOf[PDecreasesClause])
    decreasesclauses ++= method.pres.filter(pre => pre.isInstanceOf[PDecreasesClause])

    if (decreasesclauses.isEmpty) {
      errors ++= Seq(ConsistencyError("Lemma is not guaranteed to terminate. Add decreases clause.", this.pos))
    }
    var pure = method.posts.filter(post => !post.isPure)
    pure ++= method.pres.filter(pre => !pre.isPure)
    if(pure.nonEmpty && method.pres.nonEmpty){
      errors ++= Seq(ConsistencyError("Lemma is not pure", this.pos))
    }
    errors
  }
  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    group(text("lemma") <+> name <> nest(defaultIndent, parens(showVars(method.formalArgs))) <> {
      if (method.formalReturns.isEmpty) nil
      else nest(defaultIndent, line <> "returns" <+> parens(showVars(method.formalReturns)))
    }) <>
      nest(defaultIndent,
        showContracts("requires", method.pres) <>
          showContracts("ensures", method.posts)
      ) <>
      line <> (
      method.body match {
        case None =>
          nil
        case Some(actualBody) =>
          braces(nest(defaultIndent,
            lineIfSomeNonEmpty(actualBody.children) <>
              ssep(Seq(showStmt(actualBody)), line)
          ) <> line)
      })
  }

  override def name: String = method.name

  override val scopedDecls: Seq[Declaration] = method.scopedDecls

  */
}

case class OldCall(mc:MethodCall, l:Label)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt with Scope {
  override val scopedDecls = Seq()


  override lazy val prettyPrint: PrettyPrintPrimitives#Cont = {
    val call = text("oldCall") <> brackets(show(l)) <> text(mc.methodName) <> nest(defaultIndent, parens(ssep(mc.args map show, group(char(',') <> line))))
    mc.targets match {
      case Nil => call
      case _ => ssep(mc.targets map show, char(',') <> space) <+> ":=" <+> call
    }
  }

  override val extensionSubnodes: Seq[Node] = mc.args ++ mc.targets
}