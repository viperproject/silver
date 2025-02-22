// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.plugin.standard.doc

import viper.silver.plugin.SilverPlugin
import viper.silver.ast.{Program, FilePosition, NoPosition, Position}
import viper.silver.parser.{PProgram, PFieldDecl, PFields, PNode, PAnnotated, PAnnotatedExp,
  PAnnotatedStmt, PAnnotation, PAtAnnotation, PDocAnnotation, PMethod, PFunction, PStringLiteral,
  PAxiom, PSpecification, PRawString, PIdnRef, PPredicate, PDomain, PDomainFunction, Translator}
import viper.silver.ast.utility.Visitor
import upickle.default._
import java.io._
import viper.silver.frontend.SilFrontend
import viper.silver.verifier.ParseReport

case class DocReport(message: String, override val pos: Position)
  extends ParseReport(message, pos) {
  def fullId = "parser.documentation"
  def readableMessage = message
}

class DocPlugin extends SilverPlugin {

  case class DocNode(nodeType: String, info: NodeInfo, pos: (String, String), doc: String = "", children: Seq[DocNode]) {
    /** @see [[Visitor.reduceTree()]] */
    def reduceTree[T](f: (DocNode, Seq[T]) => T) = Visitor.reduceTree(this, DocNode.callSubnodes)(f)

    /** @see [[Visitor.reduceWithContext()]] */
    def reduceWithContext[C, R](context: C, enter: (DocNode, C) => C, combine: (DocNode, C, Seq[R]) => R) = {
      Visitor.reduceWithContext(this, DocNode.callSubnodes)(context, enter, combine)
    }
  }

  object DocNode {
    def callSubnodes(n: DocNode): Seq[DocNode] = n.children
    implicit lazy val rw: ReadWriter[DocNode] = macroRW
  }

  case class VarInfo(name: String, typ: String)
  case class NodeInfo(name: String = "", typ: String = "",
                      args: Seq[VarInfo] = Seq(),
                      returns: Seq[VarInfo] = Seq(),
                      misc: String = "")

  object VarInfo {
    implicit lazy val rw: ReadWriter[VarInfo] = macroRW
  }
  object NodeInfo {
    implicit lazy val rw: ReadWriter[NodeInfo] = macroRW
  }

  /** Called after identifiers have been resolved but before the parse AST is
    * translated into the normal AST.
    *
    * @param input
    *   Parse AST
    * @return
    *   Modified Parse AST
      */
  override def beforeTranslate(input: PProgram): PProgram = {
    val extractInfo: PNode => NodeInfo = {
      // case n: PFields => Map("name" -> n.toString())
      case PIdnRef(name) => NodeInfo(name)
      case PFieldDecl(idndef, colon, typ) => NodeInfo(idndef.name, typ.toString())
      case n: PMethod =>
        NodeInfo(n.idndef.name, "", n.args.inner.toSeq.map(a => VarInfo(a.idndef.name, a.typ.toString())),
                 n.returns match {
                   case Some(returns) => returns.formalReturns.inner.toSeq.map(a => VarInfo(a.idndef.name, a.typ.toString()))
                   case None => Seq() })
      case n: PFunction =>
        NodeInfo(n.idndef.name, n.resultType.toString(),
                 n.args.inner.toSeq.map(a => VarInfo(a.idndef.name, a.typ.toString())))
      case n: PPredicate => NodeInfo(n.idndef.name, "", n.args.inner.toSeq.map(a => VarInfo(a.idndef.name, a.typ.toString())))
      case n: PDomain =>
        NodeInfo(n.idndef.name, "",
                 n.typVars match {
                   case Some(typVars) => typVars.inner.toSeq.map(a => VarInfo("", a.idndef.name))
                   case None => Seq() })
      case n: PDomainFunction =>
        NodeInfo(n.idndef.name, n.resultType.toString(),
                 n.args.inner.toSeq.map(a =>
                   VarInfo(a.name match {case Some(idndef) => idndef.name case None => ""}, a.typ.toString())),
                 Seq(), n.unique match {case Some(kw) => kw.display.trim() case None => ""})
      case n: PAxiom =>
        NodeInfo(n.idndef match {case Some(id) => id.name case None => ""})
      case n: PSpecification[_] => NodeInfo(n.k.rs.display.trim())
      case _ => NodeInfo()
    }

    val extractPos: PNode => (String, String) = n => (n.pos._1.toString(), n.pos._2.toString())

    val collectDocs: Seq[PAnnotation] => String = _.collect{ case k: PAtAnnotation if (k.key.str == "doc") => k.values.inner.toSeq.map(_.str)
      case k: PDocAnnotation => Seq(k.docString.str) }.flatten.mkString("\n")
    val translator: Translator = new Translator(input);
    val extractDoc: PNode => String =
      ({
         case e: PAnnotatedExp => translator.extractAnnotation(e)._2.getOrElse("doc", Seq()).mkString("\n")
         case s: PAnnotatedStmt => translator.extractAnnotationFromStmt(s)._2.getOrElse("doc", Seq()).mkString("\n")
         case n: PAnnotated => collectDocs(n.annotations)
         case n: PSpecification[_] => collectDocs(n.annotations)
         case n: PAxiom => collectDocs(n.annotations)
         case _ => ""
       }: PNode => String)

    val removeRoots: Seq[DocNode] => Seq[DocNode] = s => s.flatMap{
      case t: DocNode if (t.nodeType == "*root*") => t.children
      case n: DocNode => Seq(n)
    }

    val docTree = input.reduceTree(
      (n: PNode, children: Seq[DocNode]) => {
        val createDocNode = ((kind: String, n: PNode) =>
          DocNode(kind, extractInfo(n), extractPos(n), extractDoc(n), removeRoots(children)))

        n match {
          case n: PIdnRef[_]                 => createDocNode("IdnRef", n)
          case n: PFieldDecl                 => createDocNode("FieldDecl", n)
          case n: PMethod                    => createDocNode("Method", n)
          case n: PFunction                  => createDocNode("Function", n)
          case n: PSpecification[_]          => createDocNode("Specification", n)
          case n: PPredicate                 => createDocNode("Predicate", n)
          case n: PDomain                    => createDocNode("Domain", n)
          case n: PAxiom                     => createDocNode("Axiom", n)
          case n: PDomainFunction            => createDocNode("DomainFunction", n)
          case _                             => DocNode("*root*", NodeInfo(), ("", ""), "", removeRoots(children))
        }
      })

    val json: String = write(docTree)
    println(json)

    PProgram(input.imported, input.members)(input.pos, DocReport(json, NoPosition) +: input.localErrors)
  }
}
