// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import viper.silver.parser.{NameAnalyser, PAnnotationsPosition, PExp, PExtender, PKeyword, PKw, PMember, PReserved, PSpecification, PStmt, PTypeSubstitution, ReformatterContext, Translator, TypeChecker}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.{Declaration, ErrorTrafo, Exp, ExtensionExp, ExtensionMember, ExtensionStmt, Info, Member, NoPosition, Node, Position, Stmt, Type}
import viper.silver.verifier.VerificationResult

import scala.collection.Set
import fastparse._

trait ParserPluginTemplate {
  import ParserPluginTemplate.Extension

  /**
    * The following variables form the main hooks for extending the parser
    */

  /**
    * The high level declarations which provide a hook for any type of independent declarations like new function or new predicates etc.
    * The high level declarations at the End Position are conservative extensions to the grammar. Extending the top level declaration using this parser
    * will not cause any effects in the pre existing parser and any other viper codes.
    *
    */
  def newDeclAtEnd : Extension[PAnnotationsPosition => PExtender with PMember] = ParserPluginTemplate.defaultExtension

  /**
    * The high level declarations that are checked at the start of the parser. These have the highest priority over
    * all the other top level declarations. A programmer can extend using this hook if any particular construct
    * if that particular top level construct is either particularly different from the top-level constructs in viper
    * or the programmer needs this particular rules to be executed with priority.
    */
  def newDeclAtStart : Extension[PAnnotationsPosition => PExtender with PMember] = ParserPluginTemplate.defaultExtension

  /**
    * The newStmt parser which is essentially an extension of the stmt rules in the new parser.
    * The statements at the End Position are conservative extensions to the grammar. Extending the statements using this parser
    * will not cause any effects in the pre existing parser and any other viper codes.
    *
    */
  def newStmtAtEnd : Extension[PStmt] = ParserPluginTemplate.defaultStmtExtension

 /**
   * The newStmt parser which is essentially an extension of the stmt rules in the new parser.
   * This provides an extension to statements that can be used force the parser to parse certain rules with high priority
   */
  def newStmtAtStart : Extension[PStmt] = ParserPluginTemplate.defaultStmtExtension

  /**
    * The newExp rule provides an extension to the expression parsers.
    * The expressions at the End Position are conservative extensions to the grammar. Extending the expressions using this parser
    * will not cause any effects in the pre existing parser and any other viper codes.
    */
  def newExpAtEnd : Extension[PExp] = ParserPluginTemplate.defaultExpExtension

/**
  * The newExp rule provides an extension to the expression parsers.
  * This provides an extension to expressions that can be used force the parser to parse certain rules with high priority
  */
  def newExpAtStart : Extension[PExp] = ParserPluginTemplate.defaultExpExtension

  /**
    * The specification rule provides an extension to the precondition expressions
    */
  def preSpecification : Extension[PSpecification[PKw.PreSpec]] =
    fp => ParserPluginTemplate.defaultExpExtension(fp).map(x => PSpecification(PReserved.implied(PKw.Requires), x)(NoPosition, NoPosition))

  /**
    * The specification rule provides an extension to the postcondition expressions
    */
  def postSpecification : Extension[PSpecification[PKw.PostSpec]] =
    fp => ParserPluginTemplate.defaultExpExtension(fp).map(x => PSpecification(PReserved.implied(PKw.Ensures), x)(NoPosition, NoPosition))

  /**
    * The specification rule provides an extension to the loop invariant specification expressions
    */
  def invSpecification : Extension[PSpecification[PKw.InvSpec]] =
    fp => ParserPluginTemplate.defaultExpExtension(fp).map(x => PSpecification(PReserved.implied(PKw.Invariant), x)(NoPosition, NoPosition))

  /**
    * This rule extends the keywords. So new strings added to the set will be considered as keywords.
    */
  def extendedKeywords = Set[PKeyword]()

  case class PExampleDeclaration()(val pos: (Position, Position)) extends PExtender{
    // The typechecker for this PAst node
    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = ???
    // These two founction for translating PAst to Ast nodes are applicable only in the case of this class being a high level declaration
    override def translateMember(t: Translator): Member = ???
    override def translateMemberSignature(t: Translator): Member = super.translateMemberSignature(t)
    override def pretty = ""
    override def reformat(ctx: ReformatterContext): Cont = ""
  }

  case class PExampleStmt()(val pos: (Position, Position)) extends PExtender with PStmt{
    //The overridden typechecker for this PAst node
    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = ???
    
    // The overridden function to translate this node to a corresponding Ast node
    override def translateStmt(t: Translator): Stmt = super.translateStmt(t)
    override def reformat(ctx: ReformatterContext): Cont = ""
  }

  case class PExampleExp()(val pos: (Position, Position)) extends PExtender with PExp{
    // These two function must be mandatorily extended due to semantic analysis rules
    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
    
    // The typecheck funtion for PAst node corresponding to the expression
    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = super.typecheck(t, n)
    // The translator function to translate the PAst node corresponding to the Ast node
    override def translateExp(t: Translator): Exp = super.translateExp(t)
    override def reformatExp(ctx: ReformatterContext): Cont = ""
  }

  /**
    * The Ast Class for the high level declarations
    * These must inherit the viper.silver.ast.ExtMember class
    */
  case class ExampleDeclaration() extends ExtensionMember{
    // All these are necessary methods for class inheritence
    override def pos: Position = ???
    override val scopedDecls: Seq[Declaration] = Seq()
    override def extensionSubnodes: Seq[Node] = ???
    override def name: String = ???
    override def errT: ErrorTrafo = ???
    override def info: Info = ???
    override def prettyPrint: PrettyPrintPrimitives#Cont = ???
  }

  /**
    * The Ast Class for the statements
    * These must inherit the viper.silver.ast.ExtensionStmt class
    */
  case class ExampleStmt() extends ExtensionStmt{
    // All these are necessary methods for class inheritence
    override def pos: Position = ???
    override def extensionSubnodes: Seq[Node] = ???
    override def errT: ErrorTrafo = ???
    override def info: Info = ???
    override def prettyPrint: PrettyPrintPrimitives#Cont = ???
    /** declarations contributed by this statement that should be added to the parent scope */
    override def declarationsInParentScope: Seq[Declaration] = ???
  }

  /**
    * The Ast Class for the expressions
    * These must inherit the viper.silver.ast.ExtensionExp class
    */
  case class ExampleExp() extends  ExtensionExp{
    override def errT: ErrorTrafo = ???
    override def info: Info = ???
    override def pos: Position = ???
    override def typ: Type = ???
    override def extensionIsPure: Boolean = ???
    override def extensionSubnodes: Seq[Node] = Seq()
    override def prettyPrint: PrettyPrintPrimitives#Cont = ???

    /**
    * This function is used to verify custom expressions.
    * This function's usage has not at all been tested and hence
    * @return viper.silver.verifier.VerificationResult
    */
    override def verifyExtExp(): VerificationResult = ???
  }
}

/**
  * A Companion Obejct that defines the default values of the parser extensions of types, PExtender(basic), PStmt(Statements)
  * and PExp(Expressions)
  */
object ParserPluginTemplate {
  type Extension[T] = P[_] => P[T]

  def combine[T](left : Extension[T], right : Extension[T]) : Extension[T] = {
    implicit ctx : P[_] => P(left(ctx) | right(ctx))
  }

  def defaultExtension : Extension[PAnnotationsPosition => PExtender with PMember] = Fail(_)
  def defaultStmtExtension : Extension[PStmt] = Fail(_)
  def defaultExpExtension : Extension[PExp] = Fail(_)
}