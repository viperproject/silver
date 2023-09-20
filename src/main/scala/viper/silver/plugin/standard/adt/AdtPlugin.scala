// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import fastparse._
import viper.silver.ast.Program
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.parser._
import viper.silver.plugin.standard.adt.encoding.AdtEncoder
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

import scala.annotation.unused

class AdtPlugin(@unused reporter: viper.silver.reporter.Reporter,
                @unused logger: ch.qos.logback.classic.Logger,
                config: viper.silver.frontend.SilFrontendConfig,
                fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{annotation, argList, formalArg, idndef, idnuse, typ, typeList, domainTypeVarDecl, ParserExtension, lineCol, _file}
  import FastParserCompanion.{ExtendedParsing, LeadingWhitespace, PositionParsing, reservedKw, reservedSym, whitespace}

  /**
    * This field is set during the beforeParse method
    */
  private var derivesImported: Boolean = false

  override def beforeParse(input: String, isImported: Boolean): String = {
    if (deactivated) {
      return input
    }

    if (!isImported) {
      // Add new parser adt declaration keyword
      ParserExtension.addNewKeywords(Set[String](PAdtKeyword.keyword, PDeriveKeyword.keyword, PWithoutKeyword.keyword))
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
  def adtDecl[$: P]: P[PAnnotationsPosition => PAdt] =
    P(P(PAdtKeyword) ~ idndef ~ typeList(domainTypeVarDecl).? ~ adtConstructorDecl.rep.braces.map(PAdtConstructors1.apply _).pos ~~~ adtDerivingDecl.lw.?).map {
      case (k, name, typparams, c, dec) =>
        ap: PAnnotationsPosition => PAdt(
          ap.annotations,
          k,
          name,
          typparams,
          PAdtSeq(c.seq.update(c.seq.inner map (c => PAdtConstructor(c.annotations, c.idndef, c.args)(PIdnRef(name.name)(name.pos))(c.pos))))(c.pos),
          dec,
        )(ap.pos)
    }

  def adtDerivingDecl[$: P] = P((P(PDeriveKeyword) ~ adtDerivingDeclBody.rep.braces.map(PAdtSeq.apply _).pos) map (PAdtDeriving.apply _).tupled).pos

  def adtWithout[$: P]: P[PAdtWithout] = P((P(PWithoutKeyword) ~ idnuse.delimited(PSym.Comma, min = 1)) map (PAdtWithout.apply _).tupled).pos

  def adtDerivingDeclBody[$: P]: P[PAdtDerivingInfo] =
    P((idnuse ~~~ typ.brackets.lw.? ~~~ adtWithout.lw.?) map ((PAdtDerivingInfo.apply _).tupled)).pos

  def adtConstructorDecl[$: P]: P[PAdtConstructor1] = P((annotation.rep ~ idndef ~ argList(formalArg) ~~~ P(PSym.Semi).lw.?) map (PAdtConstructor1.apply _).tupled).pos

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
      case pa@PAdt(anns, adt, idndef, typVars, constructors, _) if !derivesImported => PAdt(anns, adt, idndef, typVars, constructors, None)(pa.pos)
      case pa@PDomainType(idnuse, args) if declaredAdtNames.contains(idnuse.name) => PAdtType(idnuse, args)(pa.pos)
      case pc@PCall(idnuse, args, typeAnnotated) if declaredConstructorNames.exists(_.name == idnuse.name) => PConstructorCall(idnuse, args, typeAnnotated)(pc.pos)
      // A destructor call or discriminator call might be parsed as left-hand side of a field assignment, which is illegal. Hence in this case
      // we simply treat the calls as an ordinary field access, which results in an identifier not found error.
      case pfa@PAssign(Seq(fieldAcc: PFieldAccess), op, rhs) if declaredConstructorArgsNames.contains(fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) =>
        PAssign(pfa.targets.update(Seq(fieldAcc.copy(rcv = transformStrategy(fieldAcc.rcv))(fieldAcc.pos))), op, transformStrategy(rhs))(pfa.pos)
      case pfa@PFieldAccess(rcv, _, idnuse) if declaredConstructorArgsNames.contains(idnuse.name) => PDestructorCall(idnuse, rcv)(pfa.pos)
      case pfa@PFieldAccess(rcv, _, idnuse) if declaredConstructorNames.exists("is" + _.name == idnuse.name) => PDiscriminatorCall(PIdnRef(idnuse.name.substring(2))(idnuse.pos), rcv)(pfa.pos)
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

