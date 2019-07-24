// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import fastparse.noApi
import viper.silver.ast._
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.verifier.VerificationResult
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, char, parens, space, ssep, text, toParenDoc}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.rewriter.StrategyBuilder

import scala.collection.Set
import scala.util.parsing.input

class trialplugin extends SilverPlugin{

   /*
    * The import statements that instantiate the PWhiteSpaceApi class and then import the overloaded sequencing operators
    * of the "fastparse" library.
    */
  val White = PWrapper {
      import fastparse.all._
      NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  def liftPos(pos: FastPositioned): SourcePosition = {
    val start = LineColumnPosition(pos.start.line, pos.start.column)
    val end = LineColumnPosition(pos.finish.line, pos.finish.column)
    pos.start match {
      case fp: FilePosition => SourcePosition(fp.file, start, end)
      case input.NoPosition => SourcePosition(null, 0, 0)
    }
  }

   /*
    * The high level function that overloads the existing PExtender class with the PAnyFunction  and PMember traits to get a new function declaration.
    */
  case class PDoubleFunction( idndef: PIdnDef,  formalArgs: Seq[PFormalArgDecl], formalArgsSecondary: Seq[PFormalArgDecl],  rettyp: PType,  pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp]) extends PAnyFunction with PMember with PExtender{
    var classname = "PDoubleFunction"

     /*
      * The support function for the NameAnalyser phase. Not implemented by G Rahul Kranti Kiran.
      * These function were already used in the NameAnalyser in general and not just for the sake of the plugin
      * implementation.
      */
    override def getsubnodes(): Seq[PNode] ={
      Seq(this.idndef) ++ this.formalArgs ++ this.formalArgsSecondary ++ Seq(this.rettyp) ++ this.pres ++ this.posts ++ this.body
    }

     /*
      * The hook implementation for the typechecker part of the semantic analyser.
      * Must return a FastMessaging.message type variable.
      */
    override def typecheck(typechecker:TypeChecker, names: NameAnalyser): Option[Seq[String]] = {
      if (formalArgs.size == formalArgsSecondary.size){
        for(i <- 0 until formalArgs.size) {
          if (formalArgsSecondary(i).typ != formalArgs(i).typ){
            return Some(Seq(s"$classname Type mismatch at index = $i"))
          }
        }
        return None
      }
      return Some(Seq(s"$classname Argument List size mismatch"))
    }
    override def typ: PType = PPrimitiv("Bool")

     /*
      * The support functions for the translation phase.
      */
    override def translateMember(t: Translator): ExtensionMember = this match{
      case PDoubleFunction(name,formalArgs,formalArgsSecondary,_,pres,posts, body) =>
      val func1 = t.getMembers()(idndef.name).asInstanceOf[DoubleFunction]
      val ff = func1.copy(pres = pres map t.exp, posts = posts map t.exp, body = body map t.exp)(func1.pos, func1.info, func1.errT)

        ff
    }

    override def translateMemberSignature(t: Translator): ExtensionMember = {
      DoubleFunction(this.idndef.name, this.formalArgs map t.liftVarDecl, this.formalArgsSecondary map t.liftVarDecl, t.ttyp(this.rettyp), null, null, null)()
    }
  }

   /*
    * The PDoubleCall function that constitutes the ParseAst Node for the expressions that call the Double function type.
    */
  case class PDoubleCall(dfunc: PIdnUse, argList1: Seq[PExp], argList2: Seq[PExp]) extends POpApp with PExp with PExtender with PLocationAccess {

    var classname = "PDoublecall"
    override val idnuse = dfunc

     /*
      * The support functions for the nameanalyser phase.
      */
    override def args: Seq[PExp] = argList1 ++ argList2
    override def opName: String = dfunc.name
    override def signatures = if (function!=null&& function.formalArgs.size == argList1.size && function.formalArgsSecondary.size == argList2.size) function match {
      case pf: PDoubleFunction => {
        List(
          new PTypeSubstitution(argList1.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgs(i).typ) ++ argList2.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgsSecondary(i).typ) :+ (POpApp.pRes.domain.name -> function.typ))
        )
      }
    }
    else List() // this case is handled in Resolver.scala (- method check) which generates the appropriate error message
    override def forceSubstitution(ots: PTypeSubstitution) = ???

    var function : PDoubleFunction = null

    override def getsubnodes(): Seq[PNode] = {
      Seq(this.dfunc) ++ argList1 ++ argList2
    }

     /*
      * The hook implementation for the typechecker part of the Sematic Analysis phase.
      */
    override def typecheck(t: TypeChecker, names: NameAnalyser): Option[Seq[String]] = {
      val af = names.definition(t.curMember)(dfunc)
      af match {
        case ad: PDoubleFunction => {
          if (ad.formalArgs.size != argList1.size)
            return Some(Seq(s"$classname Arg List 1 are of incorrect sizes"))
          else {
            for (i <- 0 until argList1.size) {
              if (argList1(i).typ != ad.formalArgs(i).typ)
                return Some(Seq(s"Type error in ArgList1 at index=$i"))
            }
          }

          if (ad.formalArgsSecondary.size != argList2.size)
            return Some(Seq(s"$classname Arg List 1 are of incorrect sizes"))
          else {
            for (i <- 0 until argList2.size) {
              if (argList2(i).typ != ad.formalArgsSecondary(i).typ)
                return Some(Seq(s"$classname Type error in ArgList2 at index=$i"))
            }
          }

          return None
        }
        case _ => None
      }

    }

     /*
      * The tranlator for this PNode
      */
    override def translateExp(t: Translator): ExtensionExp = {
      DoubleCall(this.dfunc.name,argList1 map t.exp, argList2 map t.exp)()
    }

  }

   /*
    * The Ast Node for the declaration of the function with two parameter lists.
    * This is the translation result of the PDoubleFunction node.
    */
  case class DoubleFunction(name: String, formalArgs: Seq[LocalVarDecl], formalArgsSecondary: Seq[LocalVarDecl], typ: Type, pres: Seq[Exp], posts: Seq[Exp], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionMember {
     /*
      * Function necessary for the consistency check. Not implemented by G Rahul Kranti Kiran.
      */
    override def extensionSubnodes: Seq[Node] = {
      formalArgs ++ formalArgsSecondary ++ pres ++ posts
    }
    override def toString(): String = ""

    override val scopedDecls: Seq[Declaration] = formalArgs ++ formalArgsSecondary
  }

   /*
    * The Ast Node for the representation of the expression which call the function with two parameter lists.
    * This is the translation result of the PDoubleCall node of the ParseAst.
    */
  case class DoubleCall(funcname: String, argList1: Seq[Exp], argList2: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp{
     /*
      * The functions necessary for the consistency check in the Translation phase.
      */
    override def extensionIsPure: Boolean = {
      true
    }
    override def toString(): String = "DoubleCall"
    override def extensionSubnodes: Seq[Node] = {
      argList1 ++ argList2
    }
    override def prettyPrint: PrettyPrintPrimitives#Cont = ???
     /*
      * override def typ: Type = Type(Bool)
      */
    override def typ: Type = Translator( PProgram(Seq(),Seq(),Seq(),Seq(),Seq(),Seq(),Seq(),Seq(),Seq()) ).ttyp(PBoolLit(true).typ)

     /*
      * The functions that define the hook in the verifier(At the moment, only in Silicon).
      * Incomplete hook and has to be removed in viper.silicon.rules.evaluator.eval2()
      * for the successful compilation.
      */
    override def verifyExtExp(): viper.silver.verifier.VerificationResult = ???
  }


  lazy val doubleFunctionDecl: noApi.P[PDoubleFunction] = P(keyword("dfunction") ~/ idndef ~ "(" ~ formalArgList ~ ")"~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map{case (a, b, c, d, e, f, g) => PDoubleFunction(a, b, c, d, e, f, g)}


  lazy val dfapp: noApi.P[PDoubleCall] = P(keyword("DFCall") ~ idnuse ~ FastParser.parens(actualArgList) ~ FastParser.parens(actualArgList)).map {case (a,b,c) => PDoubleCall(a,b,c)}

/********************************************************************************************************************
  * ********************************************************************************************************
  * ***********************************************Termination Plugin***************************************
  * ********************************************************************************************************
  * ******************************************************************************************************************/

  case class PDecreases(params: Seq[PExp]) extends PExtender with PExp{
    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
    override def getsubnodes(): Seq[PNode] = params

    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
      params.map{case a => t.checkTopTyped(a,None)}
      None
    }

    override def translateExp(t: Translator): ExtensionExp = {
      val f = DecreasesTuple(params map t.exp)()
      DecreasesTuple(params map t.exp)(f.extensionSubnodes.head.pos)
    }
  }

  case class PDecreasesStar() extends PExtender with PExp{
    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???
    override def getsubnodes(): Seq[PNode] = Nil

    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
      None
    }

    override def translateExp(t: Translator): ExtensionExp = {
      DecreasesStar()()
    }
  }

  sealed trait DecreasesExp extends ExtensionExp with Node
  /**
    * Expression representing the decreases clause (termination measure).
    * @param extensionSubnodes Seq of expressions defining the termination measure (lex order)
    */
  case class DecreasesTuple(extensionSubnodes: Seq[Exp] = Nil)(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends DecreasesExp {
    override def verifyExtExp(): VerificationResult = ???
    override val extensionIsPure = true

    override val typ: Type = Bool

    /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
      * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
    override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("decreases") <> parens(ssep(extensionSubnodes map (toParenDoc(_)), char(',') <> space))
  }

  /**
    * Expression representing the decreases star option (possibly non terminating).
    * No termination checks are done.
    */
  case class DecreasesStar()(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends DecreasesExp{
    override def verifyExtExp(): VerificationResult = ???
    override val extensionIsPure: Boolean = true

    override val extensionSubnodes: Seq[Node] = Nil

    override val typ: Type = Bool

    /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
      * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
    override lazy val prettyPrint: PrettyPrintPrimitives#Cont = text("decreasesStar")

  }



  lazy val decreases: noApi.P[PExp] = P("decreasea" ~/ exp.rep(sep=",")).map{case a => PDecreases(a)}
  lazy val decreasesStar: noApi.P[PExp] = P("decreasesStar").map{_ => PDecreasesStar()}



  /********************************************************************************************************************
    * ********************************************************************************************************
    * ***********************************************Statement Expansion***************************************
    * ********************************************************************************************************
    * ******************************************************************************************************************/


  case class PDoubleMethod(idndef: PIdnDef, formalArgsList1: Seq[PFormalArgDecl], formalArgsList2: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: Option[PStmt]) extends PExtender with PMember with PGlobalDeclaration{
    override def getsubnodes(): Seq[PNode] ={
      Seq(this.idndef) ++ this.formalArgsList1 ++ this.formalArgsList2++ this.formalReturns ++ this.pres ++ this.posts ++ this.body
    }

    /*
     * The hook implementation for the typechecker part of the semantic analyser.
     * Must return a FastMessaging.message type variable.
     */
    override def typecheck(typechecker:TypeChecker, names: NameAnalyser): Option[Seq[String]] = {
      typechecker.checkMember(this) {
        (formalArgsList1 ++ formalArgsList2 ++ formalReturns) foreach (a => typechecker.check(a.typ))
      }
      typechecker.checkMember(this) {
        pres foreach (typechecker.check(_, TypeHelper.Bool))
        posts foreach (typechecker.check(_, TypeHelper.Bool))
        body.foreach(typechecker.check)
      }
      None
    }

    def deepCopy(idndef: PIdnDef = this.idndef, formalArgsList1: Seq[PFormalArgDecl] = this.formalArgsList1, formalArgsList2: Seq[PFormalArgDecl] = this.formalArgsList2, formalReturns: Seq[PFormalArgDecl] = this.formalReturns, pres: Seq[PExp] = this.pres, posts: Seq[PExp] = this.posts, body: Option[PStmt] = this.body): PDoubleMethod = {
      StrategyBuilder.Slim[PNode]({
        case m: PDoubleMethod => PDoubleMethod(idndef, formalArgsList1, formalArgsList2, formalReturns, pres, posts, body)
      }).duplicateEverything.execute[PDoubleMethod](this)
    }

    def deepCopyWithNameSubstitution(idndef: PIdnDef = this.idndef, formalArgsList1: Seq[PFormalArgDecl] = this.formalArgsList1, formalArgsList2: Seq[PFormalArgDecl] = this.formalArgsList2, formalReturns: Seq[PFormalArgDecl] = this.formalReturns, pres: Seq[PExp] = this.pres, posts: Seq[PExp] = this.posts, body: Option[PStmt] = this.body)
                                    (idn_generic_name: String, idn_substitution: String): PDoubleMethod = {
      StrategyBuilder.Slim[PNode]({
        case m: PDoubleMethod => PDoubleMethod(idndef, formalArgsList1, formalArgsList2, formalReturns, pres, posts, body)
        case PIdnDef(name) if name == idn_generic_name => PIdnDef(idn_substitution)
        case PIdnUse(name) if name == idn_generic_name => PIdnUse(idn_substitution)
      }).duplicateEverything.execute[PDoubleMethod](this)
    }

    override def translateMember(t: Translator): ExtensionMember = this match{
      case PDoubleMethod(name,_, _, _, pres, posts, body) =>
        val m = t.getMembers()(name.name).asInstanceOf[DoubleMethod]

        val newBody = body.map(actualBody => {
          val b = t.stmt(actualBody).asInstanceOf[Seqn]
          val newScopedDecls = b.scopedDecls ++ b.deepCollect {case l: Label => l}

          b.copy(scopedDecls = newScopedDecls)(b.pos, b.info, b.errT)
        })

        val finalMethod = m.copy(m.name, m.formalArgsList1, m.formalArgsList2, m.formalReturns, pres map t.exp, posts map t.exp, newBody)(m.pos, m.info, m.errT)

        t.getMembers()(m.name) = finalMethod

        finalMethod
    }

    override def translateMemberSignature(t: Translator): ExtensionMember = {
      DoubleMethod(this.idndef.name, this.formalArgsList1 map t.liftVarDecl, this.formalArgsList2 map t.liftVarDecl, this.formalReturns map t.liftVarDecl, null, null, null)(liftPos(this))
    }
  }

  case class DoubleMethod(name: String, formalArgsList1: Seq[LocalVarDecl], formalArgsList2: Seq[LocalVarDecl], formalReturns: Seq[LocalVarDecl], pres: Seq[Exp], posts: Seq[Exp], body: Option[Seqn])
                         (override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionMember{
    override def extensionSubnodes: Seq[Node] = formalArgsList1 ++ formalArgsList2 ++ formalReturns ++ pres ++ posts ++ body


    override val scopedDecls: Seq[Declaration] = formalArgsList1 ++ formalArgsList2 ++ formalReturns
  }

  case class  PDoubleMethodCall(targets: Seq[PIdnUse], method: PIdnUse, argsList1: Seq[PExp], argsList2: Seq[PExp]) extends PExtender with PStmt
  {
    override def getsubnodes(): Seq[PNode] = targets ++ Seq(method) ++ argsList1 ++ argsList2

    override def typecheck(t: TypeChecker, names: NameAnalyser): Option[Seq[String]] = {
      names.definition(t.curMember)(method) match {
        case PDoubleMethod(_, formalArgsList1, formalArgsList2, formalTargets, _, _, _) =>
          formalArgsList1.foreach(fa=>t.check(fa.typ))
          formalArgsList2.foreach(fa=>t.check(fa.typ))
          if ((formalArgsList1.length != argsList1.length) && (formalArgsList1.length != argsList1.length)) {
            Some(Seq("wrong number of arguments"))
          } else {
            if (formalTargets.length != targets.length) {
              Some(Seq("wrong number of targets"))
            } else {
              for ((formal, actual) <- (formalArgsList1 zip argsList1) ++ (formalArgsList2 zip argsList2) ++ (formalTargets zip targets)) {
                t.check(actual, formal.typ)
              }
              None
            }
          }
        case _ =>
          Some(Seq("expected a method"))
      }
    }

    override def translateStmt(t: Translator): ExtensionStmt = {
      val ts = (targets map t.exp).asInstanceOf[Seq[LocalVar]]
      DoubleMethodCall(method.name, argsList1 map t.exp, argsList2 map t.exp, ts)(liftPos(this))
    }

  }

  case class DoubleMethodCall(methodName: String, argsList1: Seq[Exp], argsList2: Seq[Exp], targets: Seq[LocalVar])(override val pos: Position = NoPosition, override val info: Info = NoInfo, override val errT: ErrorTrafo = NoTrafos) extends ExtensionStmt{
    override def extensionSubnodes: Seq[Node] = argsList1 ++ argsList2 ++ targets

    override def prettyPrint: PrettyPrintPrimitives#Cont = text("DoubleMethodCall")
  }


  lazy val doubleMethodDecl = P("dmethod" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ("returns" ~ "(" ~ formalArgList ~ ")" ).? ~/ pre.rep ~ post.rep ~ block.?).map{
    case (a,b,c,d,e,f,g) => PDoubleMethod(a,b,c,d.getOrElse(Nil),e,f,g)
  }

  lazy val dmethodCall: P[PDoubleMethodCall] = P(keyword("DMCall") ~/ (idnuse.rep(sep = ",") ~ ":=").? ~ idnuse ~ FastParser.parens(exp.rep(sep = ",")) ~ FastParser.parens(exp.rep(sep = ","))).map {
    case (None, method, args1, args2) => PDoubleMethodCall(Nil, method, args1, args2)
    case (Some(targets), method, args1, args2) => PDoubleMethodCall(targets, method, args1, args2)
  }

  /*
   * The parser rules, which extend the actual parser.
   */

   /*
    * The high level declarations which provide a hook for any type of independent declarations like new function or new predicates etc.
    */
  lazy val newDeclAtEnd = P(doubleFunctionDecl | doubleMethodDecl)


   /*
    * The newStmt parser which is essentially an extension of the stmt rules in the new parser.
    */
  lazy val newStmtAtEnd = P(dmethodCall)
   /*
    * THe newExp rule provides an extension to the expression parsers.
    */
  lazy val newExpAtEnd = P(dfapp)

  /*
   * The specification rule, though equivalent to an expression is used to extend the type of specifications
   * that are possible.
   */
  lazy val postSpecification: noApi.P[PExp] = P(decreases)
   /*
    * The extended Keywords is a set of the strings which consitute the set of keywirds but are not a part of the base keyword set.
    */
  lazy val extendedKeywords = Set[String]("dfunction", "DFCall", "dmethod", "DMCall")

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewDeclAtEnd(newDeclAtEnd)
    ParserExtension.addNewStmtAtEnd(newStmtAtEnd)
    ParserExtension.addNewExpAtEnd(newExpAtEnd)
    ParserExtension.addNewPostCondition(postSpecification)
    ParserExtension.addNewKeywords(extendedKeywords)

    input
  }

  override def beforeResolve(preP: PProgram): PProgram = {
    case class Context(increment: Int)

    val input = StrategyBuilder.RewriteNodeAndContext[PNode, Context]({
      case (t: PDomainType, ctx) => ({
        preP.extensions.find(k => k.isInstanceOf[viper.silver.plugin.PFlowDomain]) match {
          case Some(fd) =>
            val type_local = fd.asInstanceOf[viper.silver.plugin.PFlowDomain].typevar
            if(t.domain.name == type_local.idndef.name)
              viper.silver.plugin.PFlowDomainTypeUse(t.domain).asInstanceOf[PType]
            else
              t
          case None => t
        }
      }
        ,ctx)
    }, Context(1)).execute[PProgram](preP)

    input
  }

}
