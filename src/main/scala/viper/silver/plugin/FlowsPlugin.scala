// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin

import fastparse.noApi
import viper.silver.ast._
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.parser.FastParser._
import viper.silver.parser._
import viper.silver.verifier.VerificationResult
import viper.silver.ast.pretty.FastPrettyPrinter.text
import viper.silver.ast.utility.rewriter.StrategyBuilder

import scala.collection.Set

class FlowsPlugin extends ParserPluginTemplate with SilverPlugin {
  /*
   * The import statements that instantiate the PWhiteSpaceApi class and then import the overloaded sequencing operators
   * of the "fastparse" library.
   */
  override val White = PWrapper {
    import fastparse.all._
    NoTrace((("/*" ~ (!StringIn("*/") ~ AnyChar).rep ~ "*/") | ("//" ~ CharsWhile(_ != '\n').? ~ ("\n" | End)) | " " | "\t" | "\n" | "\r").rep)
  }
  import White._
  import fastparse.noApi._

  override lazy val newDeclAtEnd = P(flowDomain)
  override lazy val newExpAtEnd = P(flowDomainCall | flowDomainIdenUse)

  lazy val newAccSugar: noApi.P[PExp] = P(fieldAcc ~ "|->" ~ idnuse).map{case (a,c) => PBinExp(PAccPred(a,PFullPerm()),"&&",PBinExp(a,"==",c))}

  lazy val flowDomainIdenUse: noApi.P[PExp] = P(keyword("fdi") ~ idnuse).map{case a =>PFlowDomainIdenUse(a.name)}

  lazy val accExp: noApi.P[PExp] = P(newAccSugar/* ~ ("*" ~ accExp).?*/).map{ case b => b
  }

  lazy val fdArg= P(idndef ~ ":" ~ idnuse).map{case (a,b) => PFlowDomainArg(a,b)}

  lazy val flowDomainTypVarDecl: noApi.P[PFlowDomainTypeVarDecl] = P("type" ~/ idndef ~ "= " ~ typ ~ ";".?).map{case (a,b) => PFlowDomainTypeVarDecl(a,b)}

  lazy val flowDomainIdentity: noApi.P[PFlowDomainIdentity] = P(keyword("fdidentity") ~/ idndef ~ ";".?).map{PFlowDomainIdentity}

  lazy val flowDomainOp: noApi.P[PFlowDomainOp] = P(keyword("fdplus") ~/ "(" ~ fdArg.rep(sep =",") ~ ")" ~ ":" ~ idnuse ~
                                          post.rep ~ ("{" ~ exp ~ "}").? ).map{ case (a,b,c,d) => PFlowDomainOp(PIdnDef("fdplus"),a,PFlowDomainTypeUse(b),c,d) }


  lazy val flowDomain: noApi.P[PFlowDomain] = P(keyword("flowDomain") ~/ "{" ~ flowDomainTypVarDecl ~ flowDomainIdentity ~ flowDomainOp ~ "}").map{case (a,b,c) => PFlowDomain(a,b,c)}

  lazy val flowDomainCall: noApi.P[PFlowDomainFuncUse] = P(keyword("DFCall") ~ keyword("fdplus") ~ parens(actualArgList)).map{case(a) => PFlowDomainFuncUse(PIdnUse("fdplus"),a)}

  override lazy val extendedKeywords = Set("flowDomain", "fdidentity", "DFCall", "fdi")

  override def beforeParse(input: String, isImported: Boolean): String = {
    ParserExtension.addNewDeclAtEnd(newDeclAtEnd)
    ParserExtension.addNewExpAtEnd(newExpAtEnd)
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

/**
  * @param idndef
  * @param typ
  */
case class PFlowDomainTypeVarDecl(idndef: PIdnDef, typ: PType) extends PExtender with PUniversalDeclaration with PTypedDeclaration with PGenericType {
  override def getsubnodes(): Seq[PNode] = {
    Seq(idndef) ++ Seq(typ)
  }

  override def translateMemberSignature(t: Translator): ExtensionMember = {println("translateMemsignature of ptypevardecl"); null}

  override def translateMember(t: Translator): ExtensionMember = {
    FlowDomainTypeVarDecl(idndef.name, t.ttyp(typ))(t.liftPos(this))
  }

  override def isValidOrUndeclared: Boolean = true// An actual implementation of isValidOrUndeclared is required

  override def substitute(ts: PTypeSubstitution): PType = {println("substitute of typevardec"); null}

  override def subNodes: Seq[PType] = {println("subnodes of typecvardecl"); null}

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  override def genericName: String = idndef.name

  override def typeArguments: Seq[PType] = Seq(typ)
}

/**
  *
  * @param name
  * @param typ
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomainTypeVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)extends ExtensionMember with ExtensionType {
  override def extensionsubnodes: Seq[Node] = Seq()

  override val scopedDecls: Seq[Declaration] = Seq()

  /**
    * Takes a mapping of type variables to types and substitutes all
    * occurrences of those type variables with the corresponding type.
    */
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = {println("substitute pf typevardecl ast one"); null}

  /** Is this a concrete type (i.e. no uninstantiated type variables)? */
  override def isConcrete: Boolean = false

  override def toString(): String = "FlowDomainTypeVarDecl"

  override def getAstType = typ
}

/**
  *
  * @param idndef
  */
case class PFlowDomainIdentity(idndef: PIdnDef) extends PExtender with PUniversalDeclaration {
  override def getsubnodes(): Seq[PNode] = {
    Seq(idndef)
  }

  override def translateMemberSignature(t: Translator): ExtensionMember = super.translateMemberSignature(t)

  override def translateMember(t: Translator): ExtensionMember = {
    FlowDomainIdentity(idndef.name)(t.liftPos(this))
  }
  var typ: PType = PUnknown()
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }
}

/**
  *
  * @param name
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomainIdentity(name: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionMember {
  override def extensionsubnodes: Seq[Node] = Seq()

  override val scopedDecls: Seq[Declaration] = Seq()
}


/**
  *
  * @param idndef
  * @param flowArgs
  * @param typName
  * @param posts
  * @param body
  */
case class PFlowDomainOp(idndef: PIdnDef, flowArgs: Seq[PFlowDomainArg], typName: PFlowDomainTypeUse, posts: Seq[PExp], body: Option[PExp]) extends PExtender with PMember with PUniversalDeclaration with PTypedDeclaration {
  override def getsubnodes(): Seq[PNode] = {
    Seq(idndef) ++ Seq(typ) ++ flowArgs ++ posts ++ body
  }

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    None
  }

  def varConvert(arg: PFlowDomainArg, translator: Translator): LocalVarDecl = {
    val ttyp = translator.getMembers()(arg.typName.name).asInstanceOf[Type]
    LocalVarDecl(arg.idndef.name,ttyp)(translator.liftPos(arg.idndef))
  }

  override def translateMember(t: Translator): ExtensionMember = {
    val f = t.getMembers()(idndef.name).asInstanceOf[FlowDomainOp]
    val flowArgs_translated: Seq[LocalVarDecl] = flowArgs.map{a => varConvert(a,t)}
    FlowDomainOp(idndef.name, flowArgs_translated,t.getMembers()(typName.idnuse.name).asInstanceOf[Type], posts map t.exp, body map t.exp)(f.pos, f.info, f.errT)
  }

  override def translateMemberSignature(t: Translator): ExtensionMember = {
    FlowDomainOp(idndef.name, null, null, null, null)(t.liftPos(this))
  }

  override def typ: PType = typName.typ
}

/**
  *
  * @param name
  * @param formalArgs
  * @param typ
  * @param posts
  * @param body
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomainOp(name:String, formalArgs: Seq[LocalVarDecl], typ: Type, posts: Seq[Exp], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionMember{
  override def extensionsubnodes: Seq[Node] = formalArgs ++ Seq(typ) ++ posts ++ body

  override val scopedDecls: Seq[Declaration] = formalArgs
}

/**
  *
  * @param typevar
  * @param identity
  * @param op
  */
case class PFlowDomain(typevar: PFlowDomainTypeVarDecl,identity: PFlowDomainIdentity, op: PFlowDomainOp ) extends PExtender with PMember{
  override def getsubnodes(): Seq[PNode] = {
    Seq(typevar) ++ Seq(identity) ++ Seq(op)
  }
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this.identity.typ = this.typevar
    this.identity.typecheck(t,n)
    this.op.typecheck(t,n)
  }

  override val idndef = PIdnDef("flowDomain")

  override def translateMember(t: Translator): ExtensionMember = {
    val func1 = t.getMembers()("flowDomain").asInstanceOf[FlowDomain]

    val typevar_translated =  t.getMembers()(typevar.idndef.name).asInstanceOf[FlowDomainTypeVarDecl]
    val identity_translated = t.getMembers()(identity.idndef.name).asInstanceOf[FlowDomainIdentity]
    val op_translated = op.translateMember(t).asInstanceOf[FlowDomainOp]

    FlowDomain(typevar_translated, identity_translated, op_translated)(func1.pos, func1.info, func1.errT)
  }

  override def translateMemberSignature(t: Translator): ExtensionMember = {
    val typevar_translated = typevar.translateMember(t).asInstanceOf[FlowDomainTypeVarDecl]
    t.getMembers().put(typevar_translated.name, typevar_translated)

    val identity_translated = identity.translateMember(t).asInstanceOf[FlowDomainIdentity]
    t.getMembers().put(identity_translated.name, identity_translated)

    val op_translated = op.translateMemberSignature(t).asInstanceOf[FlowDomainOp]
    t.getMembers().put(op_translated.name, op_translated)

    FlowDomain(null, null, null)(t.liftPos(this))
  }

}

/**
  *
  * @param typevar
  * @param identity
  * @param op
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomain(typevar: FlowDomainTypeVarDecl, identity: FlowDomainIdentity, op: FlowDomainOp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)  extends ExtensionMember{
  override def extensionsubnodes: Seq[Node] = {
    Seq(typevar) ++ Seq(identity) ++ Seq(op)
  }

  override val scopedDecls: Seq[Declaration] = {
    Seq(typevar) ++ Seq(identity) ++ Seq(op)
  }

  override def name = "flowDomain1"

}


/**
  *
  * @param idnuse
  */
case class PFlowDomainTypeUse(idnuse: PIdnUse) extends PExtender with PExp with PType{
  override def typeSubstitutions: Seq[PTypeSubstitution] = {null}

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    val af = n.definition(null)(idnuse)
    af match{
      case t: PFlowDomainTypeVarDecl =>
        typ = t.typ
        typ_local = t
        None
      case _ => Some(Seq("Type of PFlowDomainTypeVarDecl not found for the given use case.Error."))
    }
  }

  var typ_local:PFlowDomainTypeVarDecl = null
  override def getsubnodes(): Seq[PNode] = Seq(idnuse)

  override def translateExp(t: Translator): ExtensionExp = {
    FlowDomainTypeUse(idnuse.name)(t.liftPos(this))
  }

  override def isValidOrUndeclared: Boolean = true

  override def substitute(ts: PTypeSubstitution): PType = {
    typ
  }

  override def subNodes: Seq[PType] = Seq()

  override def translateMember(t: Translator): ExtensionMember = {
    FlowDomainTypeVarDecl(typ_local.idndef.name, t.ttyp(typ_local.typ))(t.liftPos(this))
  }
}

/**
  *
  * @param str
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomainTypeUse(str: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with ExtensionType{
  override def extensionIsPure: Boolean = false

  override def extensionSubnodes: Seq[Node] = Seq()

  override def typ: Type = FlowDomainTypeVarDecl.asInstanceOf[Type]

  override def isSubtype(other: Type): Boolean = false
  override def isSubtype(other: Typed): Boolean = false

  override def verifyExtExp(): VerificationResult = ???

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = {println("FlowDomainTypeUse prettyprinter"); null}

  /**
    * Takes a mapping of type variables to types and substitutes all
    * occurrences of those type variables with the corresponding type.
    */
  override def substitute(typVarsMap: Map[TypeVar, Type]): Type = {println("substitute in type use "); null}

  /** Is this a concrete type (i.e. no uninstantiated type variables)? */
  override def isConcrete: Boolean = false

  override def getAstType: Type = {
    typ
  }
}

/**
  *
  * @param idndef
  * @param typName
  */
case class PFlowDomainArg(idndef: PIdnDef, typName: PIdnUse) extends PExtender with PTypedDeclaration with PLocalDeclaration{
  var local_typ: PType = PUnknown()
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] ={
    val fd = n.definition(null)(typName)
    local_typ = fd match {
      case f1: PFlowDomainTypeVarDecl => f1.typ
      case _ => return Some(Seq(s"Argument type not found in NameAnalyser. TypeChecker Error at $classname"))
    }
    None
  }
  val classname = "PFLowDomainArg"
  override def getsubnodes(): Seq[PNode] = Seq(idndef) ++ Seq(typName)
  override def typ: PType = local_typ
}

/**
  *
  * @param idnuse
  * @param args
  */
case class PFlowDomainFuncUse(idnuse: PIdnUse, args: Seq[PExp]) extends PExtender with PExp with POpApp with PLocationAccess{
  override def opName: String = idnuse.name

  override def signatures: List[PTypeSubstitution] = {println("signatures of funcuse"); null}
  val classname = "PFlowDomainFuncUse"
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    val af = n.definition(null)(idnuse)
    af match {
      case f1: PFlowDomainOp =>
        if (f1.flowArgs.size != args.size)
          return Some(Seq(s"$classname Args of incorrect sizes"))
        else {
          for (i <- 0 until args.size) {
            if (args(i).typ != f1.flowArgs(i).typ)
              return Some(Seq(s"Type error in args index=$i"))
          }
        }
    }
    args.foreach(k => if(! k.isInstanceOf[PFlowDomainIdenUse]) t.check(k,PTypeSubstitution.id))
    None
  }

  override def getsubnodes(): Seq[PNode] = {
    Seq(idnuse) ++ args
  }


  override def translateExp(t: Translator): ExtensionExp = {
    FlowDomainFuncUse("fdplus",args map t.exp)(t.liftPos(this))
  }
}

/**
  *
  * @param name
  * @param args
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomainFuncUse(name: String, args: Seq[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp{
  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = args

  override def typ: Type = FlowDomainTypeVarDecl("fd",Int)()

  override def verifyExtExp(): VerificationResult = {println("verifyExtExp printer"); null}

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = text("FlowDomainFuncUse")//println("FlowDomainFuncUse printer")
}

/**
  *
  * @param name
  */
case class PFlowDomainIdenUse(name: String) extends PExtender with PExp with PIdentifier {
  override def typeSubstitutions: Seq[PTypeSubstitution] = {null}

  override def forceSubstitution(ts: PTypeSubstitution): Unit = ???

  override def getsubnodes(): Seq[PNode] = Seq()

  var ident: PFlowDomainIdentity = null

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    ident = n.definition(null)(PIdnUse(name)).asInstanceOf[PFlowDomainIdentity]
    None
  }

  override def translateExp(t: Translator): ExtensionExp = {
    FlowDomainIdenUse(name)(t.liftPos(this))
  }
}

/**
  *
  * @param name
  * @param pos
  * @param info
  * @param errT
  */
case class FlowDomainIdenUse(name: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp{
  override def extensionIsPure: Boolean = false

  override def extensionSubnodes: Seq[Node] = Seq()

  override def typ: Type = FlowDomainTypeVarDecl("",Int)()

  override def verifyExtExp(): VerificationResult = ???

  /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
    * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
  override def prettyPrint: PrettyPrintPrimitives#Cont = null
}