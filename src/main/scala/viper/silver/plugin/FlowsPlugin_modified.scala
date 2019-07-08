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

object FlowsPlugin_modified{
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

  lazy val flowDomainTypVarDecl = P("type" ~/ idndef ~ "= " ~ typ ~ ";".?).map{case (a,b) => PTypeVarDecl(a)}
  lazy val extendedKeywords = Set[String]("flowDomain", "fdidentity", "fdplus")

  lazy val flowDomainIdentity = P(keyword("fdidentity") ~/ idndef ~ ":" ~ typ ~ ";".?).map{ case (a,b) =>
    PDomainFunction1(a,Seq(), b, false)
  }

  lazy val flowDomainOp = P(keyword("fdplus") ~/ "(" ~  formalArgList ~ ")" ~ ":" ~ typ).map{
      case (a,b) => PDomainFunction1(PIdnDef("fdplus"), a, b, false) }



  lazy val flowDomain: noApi.P[PDomain] = P(keyword("flowDomain") ~/ "{" ~ flowDomainTypVarDecl ~ flowDomainIdentity ~ flowDomainOp ~ "}").map{
    case (typevar, func1, func2) =>
      val funcs = Seq(func1) ++ Seq(func2)
      PDomain(PIdnDef("flowDomain"), Seq(typevar), funcs map (f => PDomainFunction(f.idndef, f.formalArgs, f.typ, f.unique)(PIdnUse("flowDomain")).setPos(f)),Seq())
  }
}