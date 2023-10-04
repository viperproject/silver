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

  import fp.{FP, annotation, formalArgList, idndef, idnuse, typ, typeParams, ParserExtension}

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

  private def isTerminationPluginActive: Boolean = {
    config != null && !config.disableTerminationPlugin.toOption.getOrElse(false) &&
      (!config.disableDefaultPlugins.toOption.getOrElse(false) ||
        config.plugin.toOption.getOrElse("").split(":").contains("viper.silver.plugin.standard.termination.TerminationPlugin"))
  }

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

  private def deactivated: Boolean = config != null && config.disableAdtPlugin.toOption.getOrElse(false)

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
  def adtDecl[$: P]: P[PAdt] = FP(annotation.rep(0) ~ AdtKeyword ~/ idndef ~ typeParams ~ "{" ~ adtConstructorDecl.rep ~
    "}" ~ adtDerivingDecl.?).map {
      case (pos, (anns, name, typparams, constructors, dec)) =>
        PAdt(
          name,
          typparams,
          constructors map (c => PAdtConstructor(c.idndef, c.formalArgs)(PIdnUse(name.name)(name.pos))(c.pos, c.annotations)),
          dec.getOrElse(Seq.empty)
        )(pos, anns)
    }

  def adtDerivingDecl[$: P]: P[Seq[PAdtDerivingInfo]] = P(AdtDerivesKeyword ~/ "{" ~ adtDerivingDeclBody.rep ~ "}")

  def adtDerivingDeclBody[$: P]: P[PAdtDerivingInfo] =
    FP(idnuse ~ ("[" ~ typ ~ "]").? ~ (AdtDerivesWithoutKeyword ~/ idnuse.rep(sep = ",", min = 1)).?).map {
      case (pos, (func, ttyp, bl)) => PAdtDerivingInfo(func, ttyp, bl.getOrElse(Seq.empty).toSet)(pos)
    }

  def adtConstructorDecl[$: P]: P[PAdtConstructor1] = FP(annotation.rep(0) ~ adtConstructorSignature ~ ";".?).map {
      case (pos, (anns, (name, formalArgs))) => PAdtConstructor1(name, formalArgs)(pos, anns)
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
      case pa@PAdt(idndef, typVars, constructors, _) if !derivesImported => PAdt(idndef, typVars, constructors, Seq.empty)(pa.pos, pa.annotations)
      case pa@PDomainType(idnuse, args) if declaredAdtNames.contains(idnuse.name) => PAdtType(idnuse, args)(pa.pos)
      case pc@PCall(idnuse, args, typeAnnotated) if declaredConstructorNames.exists(_.name == idnuse.name) => PConstructorCall(idnuse, args, typeAnnotated)(pc.pos)
      // A destructor call or discriminator call might be parsed as left-hand side of a field assignment, which is illegal. Hence in this case
      // we simply treat the calls as an ordinary field access, which results in an identifier not found error.
      case pfa@PAssign(Seq(fieldAcc: PFieldAccess), rhs) if declaredConstructorArgsNames.contains(fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) =>
        PAssign(Seq(PFieldAccess(transformStrategy(fieldAcc.rcv), fieldAcc.idnuse)(fieldAcc.pos)), transformStrategy(rhs))(pfa.pos)
      case pfa@PFieldAccess(rcv, idnuse) if declaredConstructorArgsNames.contains(idnuse.name) => PDestructorCall(idnuse.name, rcv)(pfa.pos)
      case pfa@PFieldAccess(rcv, idnuse) if declaredConstructorNames.exists("is" + _.name == idnuse.name) => PDiscriminatorCall(PIdnUse(idnuse.name.substring(2))(idnuse.pos), rcv)(pfa.pos)
    }).recurseFunc({
      // Stop the recursion if a destructor call or discriminator call is parsed as left-hand side of a field assignment
      case PAssign(Seq(fieldAcc: PFieldAccess), _) if declaredConstructorArgsNames.contains(fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) => Seq()
      case n: PNode => n.children collect { case ar: AnyRef => ar }
    }).execute(input)

    transformStrategy(input)
  }

  override def beforeVerify(input: Program): Program = {
    if (deactivated) {
      return input
    }
    new AdtEncoder(input).encode(isTerminationPluginActive)
  }

}

