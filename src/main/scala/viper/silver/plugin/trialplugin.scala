package viper.silver.plugin

import fastparse.noApi
import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.parser.FastParser._
import viper.silver.parser.{PFunction, _}

import scala.collection.Set

object trialplugin  /*extends PosParser[Char, String]*/ {

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
    override def translateMem(t: Translator): ExtMember = this match{
      case PDoubleFunction(name,formalArgs,formalArgsSecondary,_,pres,posts, body) =>
      val func1 = t.getMembers()(idndef.name).asInstanceOf[DoubleFunction]
      val ff = func1.copy(pres = pres map t.exp, posts = posts map t.exp, body = body map t.exp)(func1.pos, func1.info, func1.errT)

        ff
    }

    override def translateMemSignature(t: Translator): ExtMember = {
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
  case class DoubleFunction(name: String, formalArgs: Seq[LocalVarDecl], formalArgsSecondary: Seq[LocalVarDecl], typ: Type, pres: Seq[Exp], posts: Seq[Exp], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtMember {
     /*
      * Function necessary for the consistency check. Not implemented by G Rahul Kranti Kiran.
      */
    override def extensionsubnodes: Seq[Node] = {
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


   /*
    * The parser rules, which extend the actual parser.
    */

   /*
    * The high level declarations which provide a hook for any type of independent declarations like new function or new predicates etc.
    */
  lazy val newDecl = P(doubleFunctionDecl)


   /*
    * The newStmt parser wich is essentially an extension of the stmt rules in the new parser.
    */
  lazy val newStmt = P("").map {case () => "".asInstanceOf[PStmt]}
   /*
    * THe newExp rule provides an extension to the expression parsers.
    */
  lazy val newExp = P(dfapp)

  /*
   * The specification rule, though equivalent to an expression is used to extend the type of specifications
   * that are possible.
   */
  lazy val specification: noApi.P[PExp] = P("").map { case() => "".asInstanceOf[PExp]}
   /*
    * The extended Keywords is a set of the strings which consitute the set of keywirds but are not a part of the base keyword set.
    */
  lazy val extendedKeywords = Set[String]("dfunction", "DFCall")


  lazy val functionDecl2: noApi.P[PFunction] = P("function" ~/ (functionDeclWithArg | functionDeclNoArg))

  lazy val functionDeclWithArg: noApi.P[PFunction] = P(idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
  post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, g, c, d, e, f) => PFunction(a, b, c, d, e, f) }


  lazy val functionDeclNoArg: noApi.P[PFunction] = P(idndef ~ ":" ~ typ ~ pre.rep ~
  post.rep ~ ("{" ~ exp ~ "}").?).map { case (a,  c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }


  lazy val doubleFunctionDecl: noApi.P[PDoubleFunction] = P(keyword("dfunction") ~/ idndef ~ "(" ~ formalArgList ~ ")"~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
  post.rep ~ ("{" ~ exp ~ "}").?).map{case (a, b, c, d, e, f, g) => PDoubleFunction(a, b, c, d, e, f, g)}


  lazy val dfapp: noApi.P[PDoubleCall] = P(keyword("DFCall") ~ idnuse ~ parens(actualArgList) ~ parens(actualArgList)).map {case (a,b,c) => PDoubleCall(a,b,c)}



}
