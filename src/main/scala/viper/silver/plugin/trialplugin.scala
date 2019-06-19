package viper.silver.plugin

import fastparse.noApi
import viper.silver.ast
import viper.silver.ast.ExtMember
import viper.silver.parser.FastParser._
import viper.silver.parser.{PFunction, PosParser, _}

import scala.collection.Set

object trialplugin  extends PosParser[Char, String] {

  val White = PWrapper {
      import fastparse.all._
      NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  case class PDoubleFunction( idndef: PIdnDef,  formalArgs: Seq[PFormalArgDecl], formalArgsSecondary: Seq[PFormalArgDecl],  rettyp: PType,  pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp]) extends PAnyFunction with PExtender{
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

    override def translate(t: Translator): ExtMember = this match{
      case PDoubleFunction(name,formalArgs,formalArgsSecondary,_,pres,posts, body) =>
      val func1: ast.Function = t.getMembers()(idndef.asInstanceOf[PIdentifier].name).asInstanceOf[ast.Function]
      val ff: ast.Function = func1.copy(pres = pres map t.exp, posts = posts map t.exp, body = body map t.exp)(func1.pos, func1.info, func1.errT)
      ff.asInstanceOf[ExtMember]
    }
  }

  case class PStrDef(idndef: PIdnDef, value: String) extends PExp with PExtender {
    override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

    override def typeSubstitutions: Seq[PTypeSubstitution] = ???
  }

  case class PDoubleCall(dfunc: PIdnUse, argList1: Seq[PExp], argList2: Seq[PExp]) extends POpApp with PExtender with PExp with PLocationAccess {
//        override def typeSubstitutions: Seq[PTypeSubstitution] = ???
    override def args: Seq[PExp] = argList1 ++ argList2
    override def opName: String = dfunc.name
    override def idndef: PIdnDef = dfunc.name
    override val idnuse = dfunc
    override def signatures = if (function!=null&& function.formalArgs.size == argList1.size && function.formalArgsSecondary.size == argList2.size) function match{
      case pf:PDoubleFunction => {
        List(
        new PTypeSubstitution(argList1.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgs(i).typ) ++ argList2.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgsSecondary(i).typ) :+ (POpApp.pRes.domain.name -> function.typ))
      )}
    }
      else if(extfunction!=null && extfunction.formalArgs.size == args.size)( extfunction match{
        case ppa: PPredicate => List(
          new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> extfunction.formalArgs(i).typ) :+ (POpApp.pRes.domain.name -> TypeHelper.Bool))
        )
      })


    else List() // this case is handled in Resolver.scala (- method check) which generates the appropriate error message

    var function : PDoubleFunction = null
    var extfunction : PPredicate = null
    override def extraLocalTypeVariables = _extraLocalTypeVariables
    var _extraLocalTypeVariables : Set[PDomainType] = Set()
    var domainTypeRenaming : Option[PTypeRenaming] = None
    def isDomainFunction = domainTypeRenaming.isDefined
    var domainSubstitution : Option[PTypeSubstitution] = None
    override def forceSubstitution(ots: PTypeSubstitution) = {
      val ts = domainTypeRenaming match {
        case Some(dtr) =>
          val s3 = PTypeSubstitution(dtr.mm.map(kv => kv._1 -> (ots.get(kv._2) match {
            case Some(pt) => pt
            case None => PTypeSubstitution.defaultType
          })))
          assert(s3.m.keySet==dtr.mm.keySet)
          assert(s3.m.forall(_._2.isGround))
          domainSubstitution = Some(s3)
          dtr.mm.values.foldLeft(ots)(
            (tss,s)=> if (tss.contains(s)) tss else tss.add(s, PTypeSubstitution.defaultType).get)
        case _ => ots
      }
      super.forceSubstitution(ts)
      typeSubstitutions.clear(); typeSubstitutions+=ts
      typ = typ.substitute(ts)
      assert(typ.isGround)
      args.foreach(_.forceSubstitution(ts))
    }

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

  }




  lazy val functionDecl2: noApi.P[PFunction] = P("function" ~/ (functionDeclWithArg | functionDeclNoArg))

  lazy val functionDeclWithArg: noApi.P[PFunction] = P(idndef ~ "(" ~ formalArgList ~ ")" ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
          post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, g, c, d, e, f) => PFunction(a, b, c, d, e, f) }

  lazy val functionDeclNoArg: noApi.P[PFunction] = P(idndef ~ ":" ~ typ ~ pre.rep ~
    post.rep ~ ("{" ~ exp ~ "}").?).map { case (a,  c, d, e, f) => PFunction(a, Seq[PFormalArgDecl](), c, d, e, f) }


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
