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

import scala.collection.Set
import scala.util.parsing.input

object FlowsPlugin{
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

  lazy val newDecl = P(flowDomain)
  lazy val  newStmt = P("somethingOfaStmt").map{case () => "".asInstanceOf[PStmt]}
  lazy val newExp = P(flowDomainCall | flowDomainIdenUse)
  lazy val preSpecification: noApi.P[PExp] = P("preConditionSpecificationExample").map{case() => "".asInstanceOf[PExp]}
  lazy val postSpecification: noApi.P[PExp] = P("postConditionSpecificationExample").map{case() => "".asInstanceOf[PExp]}
  lazy val invSpecification: noApi.P[PExp] = P("invariantSpecificationExample").map{case() => "".asInstanceOf[PExp]}

  def liftPos(pos: FastPositioned): SourcePosition = {
    val start = LineColumnPosition(pos.start.line, pos.start.column)
    val end = LineColumnPosition(pos.finish.line, pos.finish.column)
    pos.start match {
      case fp: FilePosition => SourcePosition(fp.file, start, end)
      case input.NoPosition => SourcePosition(null, 0, 0)
    }
  }

  lazy val newAccSugar: noApi.P[PExp] = P(fieldAcc ~ "|->" ~ idnuse).map{case (a,c) => PBinExp(PAccPred(a,PFullPerm()),"&&",PBinExp(a,"==",c))}

  lazy val flowDomainIdenUse: noApi.P[PExp] = P(keyword("fdi") ~ idnuse).map{PFlowDomainIdenUse}

  lazy val accExp: noApi.P[PExp] = P(newAccSugar/* ~ ("*" ~ accExp).?*/).map{ case b => b
  }

  lazy val fdArg= P(idndef ~ ":" ~ idnuse).map{case (a,b) => PFlowDomainArg(a,b)}

  lazy val flowDomainTypVarDecl: noApi.P[PFlowDomainTypeVarDecl] = P("type" ~/ idndef ~ "= " ~ typ ~ ";".?).map{case (a,b) => PFlowDomainTypeVarDecl(a,b)}

  lazy val flowDomainIdentity: noApi.P[PFlowDomainIdentity] = P(keyword("fdidentity") ~/ idndef ~ ";".?).map{PFlowDomainIdentity}

  lazy val flowDomainOp: noApi.P[PFlowDomainOp] = P(keyword("fdplus") ~/ "(" ~ fdArg.rep(sep =",") ~ ")" ~ ":" ~ idnuse ~
                                          post.rep ~ ("{" ~ exp ~ "}").? ).map{ case (a,b,c,d) => PFlowDomainOp(PIdnDef("fdplus"),a,PFlowDomainTypeUse(b),c,d) }


  lazy val flowDomain: noApi.P[PFlowDomain] = P(keyword("flowDomain") ~/ "{" ~ flowDomainTypVarDecl ~ flowDomainIdentity ~ flowDomainOp ~ "}").map{case (a,b,c) => PFlowDomain(a,b,c)}

  lazy val flowDomainCall: noApi.P[PFlowDomainFuncUse] = P(keyword("DFCall") ~ keyword("fdplus") ~ parens(actualArgList)).map{case(a) => PFlowDomainFuncUse(PIdnUse("fdplus"),a)}

  lazy val extendedKeywords = Set("flowDomain", "fdidentity", "fdplus", "DFCall", "fdi")


  /**
    * @param idndef
    * @param typ
    */
  case class PFlowDomainTypeVarDecl(idndef: PIdnDef, typ: PType) extends PExtender with PUniversalDeclaration with PTypedDeclaration with PGenericType {
    override def getsubnodes(): Seq[PNode] = {
      Seq(idndef) ++ Seq(typ)
    }

    override def translateMemSignature(t: Translator): ExtMember = {println("printedhere"); null}

    override def translateMem(t: Translator): ExtMember = {
      FlowDomainTypeVarDecl(idndef.name, t.ttyp(typ))(liftPos(this))
    }

    override def isValidOrUndeclared: Boolean = true// An actual implementation of isValidOrUndeclared is required

    override def substitute(ts: PTypeSubstitution): PType = {println("printedhere"); null}

    override def subNodes: Seq[PType] = {println("printedhere"); null}

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
  case class FlowDomainTypeVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)extends ExtMember with Type{
    override def extensionsubnodes: Seq[Node] = Seq(typ)

    override val scopedDecls: Seq[Declaration] = Seq()

    /**
      * Takes a mapping of type variables to types and substitutes all
      * occurrences of those type variables with the corresponding type.
      */
    override def substitute(typVarsMap: Map[TypeVar, Type]): Type = {println("printedhere"); null}

    /** Is this a concrete type (i.e. no uninstantiated type variables)? */
    override def isConcrete: Boolean = false
  }

  /**
    *
    * @param idndef
    */
  case class PFlowDomainIdentity(idndef: PIdnDef) extends PExtender with PUniversalDeclaration {
    override def getsubnodes(): Seq[PNode] = {
      Seq(idndef)
    }
//    override def name = idndef.name

    override def translateMemSignature(t: Translator): ExtMember = super.translateMemSignature(t)

    override def translateMem(t: Translator): ExtMember = {
      FlowDomainIdentity(idndef.name)(liftPos(this))
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
  case class FlowDomainIdentity(name: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtMember {
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
      LocalVarDecl(arg.idndef.name,ttyp)(liftPos(arg.idndef))
    }

    override def translateMem(t: Translator): ExtMember = {
      val f = t.getMembers()(idndef.name).asInstanceOf[FlowDomainOp]
      val flowArgs_translated: Seq[LocalVarDecl] = flowArgs.map{a => varConvert(a,t)}
      FlowDomainOp(idndef.name, flowArgs_translated,t.getMembers()(typName.idnuse.name).asInstanceOf[Type], posts map t.exp, body map t.exp)(f.pos, f.info, f.errT)
    }

    override def translateMemSignature(t: Translator): ExtMember = {
      FlowDomainOp(idndef.name, null, null, null, null)(liftPos(this))
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
  case class FlowDomainOp(name:String, formalArgs: Seq[LocalVarDecl], typ: Type, posts: Seq[Exp], body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtMember{
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
      None
    }

    override val idndef = PIdnDef("flowDomain")

    override def translateMem(t: Translator): ExtMember = {
      val func1 = t.getMembers()("flowDomain").asInstanceOf[FlowDomain]

      val typevar_translated =  t.getMembers()(typevar.idndef.name).asInstanceOf[FlowDomainTypeVarDecl]
      val identity_translated = t.getMembers()(identity.idndef.name).asInstanceOf[FlowDomainIdentity]
      val op_translated = op.translateMem(t).asInstanceOf[FlowDomainOp]

      FlowDomain(typevar_translated, identity_translated, op_translated)(func1.pos, func1.info, func1.errT)
    }

    override def translateMemSignature(t: Translator): ExtMember = {
      val typevar_translated = typevar.translateMem(t).asInstanceOf[FlowDomainTypeVarDecl]
      t.getMembers().put(typevar_translated.name, typevar_translated)

      val identity_translated = identity.translateMem(t).asInstanceOf[FlowDomainIdentity]
      t.getMembers().put(identity_translated.name, identity_translated)

      val op_translated = op.translateMemSignature(t).asInstanceOf[FlowDomainOp]
      t.getMembers().put(op_translated.name, op_translated)

      FlowDomain(null, null, null)(liftPos(this))
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
  case class FlowDomain(typevar: FlowDomainTypeVarDecl, identity: FlowDomainIdentity, op: FlowDomainOp)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)  extends ExtMember{
    override def extensionsubnodes: Seq[Node] = {
      Seq(typevar) ++ Seq(identity) ++ Seq(op)
    }

    override val scopedDecls: Seq[Declaration] = {
       Seq(typevar) ++ Seq(identity) ++ Seq(op)
    }

    override def name = "flowDomain"

  }


  /**
    *
    * @param idnuse
    */
  case class PFlowDomainTypeUse(idnuse: PIdnUse) extends PExtender with PExp with PType{
    override def typeSubstitutions: Seq[PTypeSubstitution] = {null}

    override def forceSubstitution(ts: PTypeSubstitution): Unit = {null}

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
      FlowDomainTypeUse(idnuse.name)(liftPos(this))
    }

    override def isValidOrUndeclared: Boolean = true

    override def substitute(ts: PTypeSubstitution): PType = {
      typ
    }

    override def subNodes: Seq[PType] = Seq()

    override def translateMem(t: Translator): ExtMember = {
      FlowDomainTypeVarDecl(typ_local.idndef.name, t.ttyp(typ_local.typ))(liftPos(this))
    }
  }

  /**
    *
    * @param str
    * @param pos
    * @param info
    * @param errT
    */
  case class FlowDomainTypeUse(str: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp with Type{
    override def extensionIsPure: Boolean = true

    override def extensionSubnodes: Seq[Node] = Seq()

    override def typ: Type = FlowDomainTypeVarDecl.asInstanceOf[Type]

    override def isSubtype(other: Type): Boolean = false
    override def isSubtype(other: Typed): Boolean = false

    override def verifyExtExp(): VerificationResult = {println("printedhere"); null}

    /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
      * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
    override def prettyPrint: PrettyPrintPrimitives#Cont = {println("printedhere"); null}

    /**
      * Takes a mapping of type variables to types and substitutes all
      * occurrences of those type variables with the corresponding type.
      */
    override def substitute(typVarsMap: Map[TypeVar, Type]): Type = {println("printedhere"); null}

    /** Is this a concrete type (i.e. no uninstantiated type variables)? */
    override def isConcrete: Boolean = false
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

    override def signatures: List[PTypeSubstitution] = {println("printedhere"); null}
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
      FlowDomainFuncUse("fdplus",args map t.exp)(liftPos(this))
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

    override def typ: Type = {println("printedhere"); null}

    override def verifyExtExp(): VerificationResult = {println("printedhere"); null}

    /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
      * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
    override def prettyPrint: PrettyPrintPrimitives#Cont = {println("printedhere"); null}
  }

  /**
    *
    * @param idnuse
    */
  case class PFlowDomainIdenUse(idnuse: PIdnUse) extends PExtender with PExp with PIdentifier {
    override def typeSubstitutions: Seq[PTypeSubstitution] = {null}

    override def forceSubstitution(ts: PTypeSubstitution): Unit = {null}

    var ident: PFlowDomainIdentity = null

    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
      ident = n.definition(null)(idnuse).asInstanceOf[PFlowDomainIdentity]
      None
    }

    override def translateExp(t: Translator): ExtensionExp = {
      FlowDomainIdenUse(name)(liftPos(this))
    }

    override def name: String = idnuse.name
  }

  /**
    *
    * @param name
    * @param pos
    * @param info
    * @param errT
    */
  case class FlowDomainIdenUse(name: String)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionExp{
    override def extensionIsPure: Boolean = true

    override def extensionSubnodes: Seq[Node] = Seq()

    override def typ: Type = local_typ
    var local_typ: FlowDomainTypeVarDecl = null

    override def verifyExtExp(): VerificationResult = {println("printedhere"); null}

    /** Pretty printing functionality as defined for other nodes in class FastPrettyPrinter.
      * Sample implementation would be text("old") <> parens(show(e)) for pretty-printing an old-expression. */
    override def prettyPrint: PrettyPrintPrimitives#Cont = {println("printedhere"); null}
  }
}