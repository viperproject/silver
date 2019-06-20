package viper.silver.plugin

import fastparse.noApi
import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.parser.FastParser._
import viper.silver.parser.{PFunction, PosParser, _}
import viper.silver.verifier.ParseReport

import scala.collection.Set

object trialplugin  extends PosParser[Char, String] {

  val White = PWrapper {
      import fastparse.all._
      NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  case class PDoubleFunction( idndef: PIdnDef,  formalArgs: Seq[PFormalArgDecl], formalArgsSecondary: Seq[PFormalArgDecl],  rettyp: PType,  pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp]) extends PAnyFunction with PMember with PExtender{
    override def getsubnodes(): Seq[PNode] ={
      Seq(this.idndef) ++ this.formalArgs ++ this.formalArgsSecondary ++ Seq(this.rettyp) ++ this.pres ++ this.posts ++ this.body
    }
    override def typ: PType = PPrimitiv("Bool")

    /**
      * Must return a FastMessaging.message type variable
      */

    override def typecheck(typechecker:TypeChecker, names: NameAnalyser): Option[String] = {
      if (formalArgs.size == formalArgsSecondary.size){
        for(i <- 0 until formalArgs.size) {
          if (formalArgsSecondary(i).typ != formalArgs(i).typ){
            return Some(s"Type mismatch at index = $i")
          }
        }
        return None
      }
      return Some("Argument List size mismatch")
    }

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

  case class DoubleFunction(name: String, formalArgs: Seq[LocalVarDecl], formalArgsSecondary: Seq[LocalVarDecl], typ: Type, pres: Seq[Exp], posts: Seq[Exp], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtMember {
    override def extensionsubnodes: Seq[Node] = {
      formalArgs ++ formalArgsSecondary ++ pres ++ posts
    }

    override val scopedDecls: Seq[Declaration] = formalArgs ++ formalArgsSecondary
  }

  case class DoubleCall(funcname: String, argList1: Seq[Exp], argList2: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp{
    override def extensionIsPure: Boolean = {
      true
    }

    override def extensionSubnodes: Seq[Node] = {
      argList1 ++ argList2
    }

    override def prettyPrint: PrettyPrintPrimitives#Cont = ???
    override def typ: Type = Translator( PProgram(Seq(),Seq(),Seq(),Seq(),Seq(),Seq(),Seq(),Seq[PExtender](),Seq[ParseReport]()) ).ttyp(PBoolLit(true).typ)
  }

  case class PDoubleCall(dfunc: PIdnUse, argList1: Seq[PExp], argList2: Seq[PExp]) extends POpApp with PExp with PExtender with PLocationAccess {
//        override def typeSubstitutions: Seq[PTypeSubstitution] = ???
    override def args: Seq[PExp] = argList1 ++ argList2
    override def opName: String = dfunc.name
    override val idnuse = dfunc
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

    override def typecheck(t: TypeChecker, names: NameAnalyser): Option[String] = {
      val af = names.definition(t.curMember)(dfunc)
      af match {
        case ad: PDoubleFunction => {
          print(ad.typ)
          if (ad.formalArgs.size != argList1.size)
            return Some("Arg List 1 are of incorrect sizes")
          else {
            for (i <- 0 until argList1.size) {
              if (argList1(i).typ != ad.formalArgs(i).typ)
                return Some(s"Type error in ArgList1 at index=$i")
            }
          }

          if (ad.formalArgsSecondary.size != argList2.size)
            return Some("Arg List 1 are of incorrect sizes")
          else {
            for (i <- 0 until argList2.size) {
              if (argList2(i).typ != ad.formalArgsSecondary(i).typ)
                return Some(s"Type error in ArgList2 at index=$i")
            }
          }

          return None
        }
        case _ => None
      }

    }

    override def translateExp(t: Translator): ExtensionExp = {
      DoubleCall(this.dfunc.name,argList1 map t.exp, argList2 map t.exp)()
    }

  }

  lazy val functionDecl2: noApi.P[PFunction] = P("function" ~/ (functionDeclWithArg | functionDeclNoArg))


  lazy val functionDeclWithArg: noApi.P[PFunction] = P(idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
          post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, g, c, d, e, f) => PFunction(a, b, c, d, e, f) }

  lazy val functionDeclNoArg: noApi.P[PFunction] = P(idndef ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map { case (a,  c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }

  case class PStrDef(idndef: PIdnDef, value: String) extends PExtensionExp {
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
  }


  lazy val doubleFunctionDecl: noApi.P[PDoubleFunction] = P(keyword("dfunction") ~/ idndef ~ "(" ~ formalArgList ~ ")"~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map{case (a, b, c, d, e, f, g) => PDoubleFunction(a, b, c, d, e, f, g)}

  lazy val stringtyp: noApi.P[PType] = P("String" ~~ !identContinues).!.map(PPrimitiv)

  lazy val newDecl = P(doubleFunctionDecl)

  lazy val stringDef: noApi.P[PStrDef] = P(stringtyp ~/ idndef ~ ":=" ~ "\"" ~ (AnyChar.rep).! ~ "\"").map{case(_, b,c) => PStrDef(b, c)}

  lazy val dfapp: noApi.P[PDoubleCall] = P(keyword("DFCall") ~ idnuse ~ parens(actualArgList) ~ parens(actualArgList)).map {case (a,b,c) => PDoubleCall(a,b,c)}

  // This newStmt extension is not yet used
  lazy val newStmt = P(block)
  lazy val newExp = P(stringDef | dfapp)

  lazy val extendedKeywords = Set[String]("dfunction", "DFCall")


}
