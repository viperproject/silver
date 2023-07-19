// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import fastparse._
import viper.silver.ast.Program
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.parser.FastParserCompanion.whitespace
import viper.silver.parser._
import viper.silver.plugin.standard.adt.encoding.AdtEncoder
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

import scala.annotation.unused

class AdtPlugin(@unused reporter: viper.silver.reporter.Reporter,
                @unused logger: ch.qos.logback.classic.Logger,
                config: viper.silver.frontend.SilFrontendConfig,
                fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{annotation, FP, formalArgList, idndef, idnuse, keywordLang, typ, typeParams, ParserExtension}

  /**
    * Keywords used to define ADT's
    */
  private val AdtKeyword: String = "adt"
  private val AdtDerivesKeyword: String = "derives"
  private val AdtDerivesWithoutKeyword: String = "without"
  /**
    * This field is set during the beforeParse method
    */
  private var derivesImported: Boolean = false

  def adtDerivingFunc[$: P]: P[PIdnUse] = FP(StringIn("contains").!).map { case (pos, id) => PIdnUse(id)(pos) }

  override def beforeParse(input: String, isImported: Boolean): String = {
    if (deactivated) {
      return input
    }

    if (!isImported) {
      // Add new parser adt declaration keyword
      ParserExtension.addNewKeywords(Set[String](AdtKeyword))
      // Add new parser for adt declaration
      ParserExtension.addNewDeclAtEnd(adtDecl(_))
    }
    setDerivesImported(input)
    input
  }

  private def deactivated: Boolean = config != null && config.adtPlugin.toOption.getOrElse(false)

  private def setDerivesImported(input: String): Unit = "import[\\s]+<adt\\/derives\\.vpr>".r.findFirstIn(input) match {
    case Some(_) => derivesImported = true
    case None =>
  }

  /**
    * Parser for ADT declaration.
    *
    * Example of a List:
    *
    * adt List[T] {
    *   Nil()
    *   Cons(value: T, tail: List[T])
    * }
    *
    */
  def adtDecl[$: P]: P[PAnnotationsPosition => PAdt] = P(keywordLang(AdtKeyword) ~ idndef ~ typeParams ~ "{" ~ adtConstructorDecl.rep ~
    "}" ~ adtDerivingDecl.?).map {
    case (k, name, typparams, constructors, dec) =>
      ap: PAnnotationsPosition => PAdt(
        ap.annotations,
        k,
        name,
        typparams,
        constructors map (c => PAdtConstructor(c.annotations, c.idndef, c.formalArgs)(PIdnUse(name.name)(name.pos))(c.pos)),
        dec.map(_._1),
        dec.map(_._2).getOrElse(Seq.empty)
      )(ap.pos)
  }

  def adtDerivingDecl[$: P]: P[(PKeywordLang, Seq[PAdtDerivingInfo])] = P(keywordLang(AdtDerivesKeyword) ~/ "{" ~ adtDerivingDeclBody.rep ~ "}")

  def adtDerivingDeclBody[$: P]: P[PAdtDerivingInfo] =
    FP(idnuse ~ ("[" ~ typ ~ "]").? ~ (keywordLang(AdtDerivesWithoutKeyword) ~/ idnuse.rep(sep = ",", min = 1)).?).map {
    case (pos, (func, ttyp, Some((without, bl)))) => PAdtDerivingInfo(func, ttyp, Some(without), bl.toSet)(pos)
    case (pos, (func, ttyp, None)) => PAdtDerivingInfo(func, ttyp, None, Set.empty)(pos)
  }

  def adtConstructorDecl[$: P]: P[PAdtConstructor1] = FP(annotation.rep(0) ~ adtConstructorSignature ~ ";".?).map {
    case (pos, (anns, (name, formalArgs))) => PAdtConstructor1(anns, name, formalArgs)(pos)
  }

  def adtConstructorSignature[$: P]: P[(PIdnDef, Seq[PFormalArgDecl])] = P(idndef ~ "(" ~ formalArgList ~ ")")

  override def beforeResolve(input: PProgram): PProgram = {
    if (deactivated) {
      return input
    }
    // Syntax of adt types, adt constructor calls and destructor calls can not be distinguished from ordinary
    // viper syntax, hence we need the following transforming step before resolving.
    val declaredAdtNames = input.extensions.collect { case a: PAdt => a.idndef.name }.toSet
    val declaredConstructorNames = input.extensions.collect { case a: PAdt => a.constructors.map(c => c.idndef) }.flatten.toSet
    val declaredConstructorArgsNames = input.extensions.collect { case a: PAdt =>
      a.constructors flatMap (c => c.formalArgs collect { case PFormalArgDecl(idndef, _) => idndef.name })
    }.flatten.toSet

    def transformStrategy[T <: PNode](input: T): T = StrategyBuilder.Slim[PNode]({
      // If derives import is missing deriving info is ignored
      case pa@PAdt(anns, adt, idndef, typVars, constructors, derive, _) if !derivesImported => PAdt(anns, adt, idndef, typVars, constructors, derive, Seq.empty)(pa.pos)
      case pa@PDomainType(idnuse, args) if declaredAdtNames.contains(idnuse.name) => PAdtType(idnuse, args)(pa.pos)
      case pc@PCall(idnuse, args, typeAnnotated) if declaredConstructorNames.exists(_.name == idnuse.name) => PConstructorCall(idnuse, args, typeAnnotated)(pc.pos)
      // A destructor call or discriminator call might be parsed as left-hand side of a field assignment, which is illegal. Hence in this case
      // we simply treat the calls as an ordinary field access, which results in an identifier not found error.
      case pfa@PAssign(Seq(fieldAcc: PFieldAccess), op, rhs) if declaredConstructorArgsNames.contains(fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) =>
        PAssign(Seq(PFieldAccess(transformStrategy(fieldAcc.rcv), fieldAcc.idnuse)(fieldAcc.pos)), op, transformStrategy(rhs))(pfa.pos)
      case pfa@PFieldAccess(rcv, idnuse) if declaredConstructorArgsNames.contains(idnuse.name) => PDestructorCall(idnuse, rcv)(pfa.pos)
      case pfa@PFieldAccess(rcv, idnuse) if declaredConstructorNames.exists("is" + _.name == idnuse.name) => PDiscriminatorCall(PIdnUse(idnuse.name.substring(2))(idnuse.pos), rcv)(pfa.pos)
    }).recurseFunc({
      // Stop the recursion if a destructor call or discriminator call is parsed as left-hand side of a field assignment
      case PAssign(Seq(fieldAcc: PFieldAccess), _, _) if declaredConstructorArgsNames.contains(fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) => Seq()
      case n: PNode => n.children collect { case ar: AnyRef => ar }
    }).execute(input)

    transformStrategy(input)
  }

  override def beforeVerify(input: Program): Program = {
    if (deactivated) {
      return input
    }
    new AdtEncoder(input).encode()
  }

}

