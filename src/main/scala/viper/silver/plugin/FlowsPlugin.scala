package viper.silver.plugin

import fastparse.noApi
import viper.silver.ast._
import viper.silver.parser.FastParser._
import viper.silver.parser._
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
  lazy val newStmt = P("somethingOfaStmt").map{case () => "".asInstanceOf[PStmt]}
  lazy val newExp = P("somethingOfanExp").map{case () => "".asInstanceOf[PExp]}
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

  lazy val flowDomainTypVarDecl: noApi.P[PFlowDomainTypeVarDecl] = P("type" ~/ idndef ~ "= " ~ typ ~ ";".?).map{case (a,b) => PFlowDomainTypeVarDecl(a,b)}

  lazy val flowDomainIdentity: noApi.P[PFlowDomainIdentity] = P(keyword("fdidentity") ~/ idndef ~ ";".?).map{PFlowDomainIdentity}

  lazy val flowDomainOp: noApi.P[PFlowDomainOp] = P(keyword("fdplus") ~/ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~
                                          post.rep ~ ("{" ~ exp ~ "}").? ).map{ case (a,b,c,d) => PFlowDomainOp(PIdnDef("fdplus"),a,b,c,d) }


  lazy val flowDomain: noApi.P[PFlowDomain] = P(keyword("flowDomain") ~/ "{" ~ flowDomainTypVarDecl ~ flowDomainIdentity ~ flowDomainOp ~ "}").map{case (a,b,c) => PFlowDomain(a,b,c)}

  lazy val extendedKeywords = Set[String]("flowDomain", "fdidentity", "fdplus")


  /**
    *
    * @param idndef
    * @param typ
    */
  case class PFlowDomainTypeVarDecl(idndef: PIdnDef, typ: PType) extends PExtender with PGlobalDeclaration  with PType {
    override def getsubnodes(): Seq[PNode] = {
      Seq(idndef) ++ Seq(typ)
    }

    override def translateMemSignature(t: Translator): ExtMember = ???

    override def translateMem(t: Translator): ExtMember = {
      FlowDomainTypeVarDecl(idndef.name, t.ttyp(typ))(liftPos(this))
    }

    override def isValidOrUndeclared: Boolean = true// An actual implementation of isValidOrUndeclared is required

    override def substitute(ts: PTypeSubstitution): PType = ???

    override def subNodes: Seq[PType] = ???

    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
      None
    }
  }

  /**
    *
    * @param name
    * @param typ
    * @param pos
    * @param info
    * @param errT
    */
  case class FlowDomainTypeVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos)extends ExtMember{
    override def extensionsubnodes: Seq[Node] = Seq(typ)

    override val scopedDecls: Seq[Declaration] = Seq()
  }

  /**
    *
    * @param idndef
    */
  case class PFlowDomainIdentity(idndef: PIdnDef) extends PExtender with PGlobalDeclaration{
    override def getsubnodes(): Seq[PNode] = {
      Seq(idndef)
    }

    override def translateMemSignature(t: Translator): ExtMember = super.translateMemSignature(t)

    override def translateMem(t: Translator): ExtMember = {
      FlowDomainIdentity(idndef.name)(liftPos(this))
    }

    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = super.typecheck(t, n)
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
    * @param formalArgs
    * @param typ
    * @param posts
    * @param body
    */
  case class PFlowDomainOp(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, posts: Seq[PExp], body: Option[PExp]) extends PExtender with PAnyFunction{
    override def getsubnodes(): Seq[PNode] = {
      Seq(idndef) ++ Seq(typ) ++ formalArgs ++ posts ++ body
    }

    def liftVarDecl(formal: PFormalArgDecl,t: Translator){
      val type_translated =
      LocalVarDecl(formal.idndef.name, type_translated)(formal.idndef)
    }

    override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = super.typecheck(t, n)

    override def translateMem(t: Translator): ExtMember ={
      val f = t.getMembers()(idndef.name).asInstanceOf[FlowDomainOp]
      val formalArgsTranslated = formalArgs foreach liftVarDecl(_,t)

      FlowDomainOp(idndef.name, formalArgsTranslated ,t.ttyp(typ), posts map t.exp, body map t.exp)(f.pos, f.info, f.errT)
    }

    override def translateMemSignature(t: Translator): ExtMember = {
      FlowDomainOp(idndef.name,null, null, null, null)(liftPos(this))
    }

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

}