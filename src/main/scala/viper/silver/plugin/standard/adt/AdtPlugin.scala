// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import fastparse._
import viper.silver.ast.Program
import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.parser.FastParser.{FP, anyFormalArgList, idndef, whitespace}
import viper.silver.parser._
import viper.silver.plugin.standard.adt.encoding.AdtEncoder
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}


class AdtPlugin extends SilverPlugin with ParserPluginTemplate {

  /**
    * Keyword used to define ADT's
    */
  private val AdtKeyword: String = "adt"

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
  def adtDecl[_: P]: P[PAdt] = FP(AdtKeyword ~/ idndef ~ ("[" ~ adtTypeVarDecl.rep(sep = ",") ~ "]").? ~ "{" ~ adtConstructorDecl.rep ~
    "}").map {
    case (pos, (name, typparams, constructors)) =>
      PAdt(
        name,
        typparams.getOrElse(Nil),
        constructors map (c => PAdtConstructor(c.idndef, c.formalArgs)(PIdnUse(name.name)(name.pos))(c.pos)))(pos)
  }

  def adtTypeVarDecl[_: P]: P[PTypeVarDecl] = FP(idndef).map{ case (pos, i) => PTypeVarDecl(i)(pos) }

  def adtConstructorDecl[_: P]: P[PAdtConstructor1] = FP(adtConstructorSignature ~ ";".?).map {
    case (pos, cdecl) => cdecl match {
      case (name, formalArgs) => PAdtConstructor1(name, formalArgs)(pos)
    }
  }

  def adtConstructorSignature[_: P]: P[(PIdnDef, Seq[PAnyFormalArgDecl])] = P(idndef ~ "(" ~ anyFormalArgList ~ ")")

  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new parser adt declaration keyword
    ParserExtension.addNewKeywords(Set[String](AdtKeyword))
    // Add new parser for adt declaration
    ParserExtension.addNewDeclAtEnd(adtDecl(_))
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    // Syntax of adt types, adt constructor calls and destructor calls can not be distinguished from ordinary
    // viper syntax, hence we need the following transforming step before resolving.
    val declaredAdtNames = input.extensions.collect { case a: PAdt => a.idndef }.toSet
    val declaredConstructorNames = input.extensions.collect { case a: PAdt => a.constructors.map(c => c.idndef) }.flatten.toSet
    val declaredConstructorArgsNames = input.extensions.collect { case a: PAdt =>
      a.constructors flatMap ( c => c.formalArgs collect {case PFormalArgDecl(idndef, _) => idndef})}.flatten.toSet
    def transformStrategy[T <: PNode](input: T): T = StrategyBuilder.Slim[PNode]({
      case pa@PDomainType(idnuse, args) if declaredAdtNames.exists(_.name == idnuse.name) => PAdtType(idnuse, args)(pa.pos)
      case pc@PCall(idnuse, args, typeAnnotated) if declaredConstructorNames.exists(_.name == idnuse.name) => PConstructorCall(idnuse, args, typeAnnotated)(pc.pos)
      // A destructor call or discriminator call might be parsed as left-hand side of a field assignment, which is illegal. Hence in this case
      // we simply treat the calls as an ordinary field access, which results in an identifier not found error.
      case pfa@PFieldAssign(fieldAcc, rhs) if declaredConstructorArgsNames.exists(_.name == fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) =>
          PFieldAssign(PFieldAccess(transformStrategy(fieldAcc.rcv), fieldAcc.idnuse)(fieldAcc.pos), transformStrategy(rhs))(pfa.pos)
      case pfa@PFieldAccess(rcv, idnuse) if declaredConstructorArgsNames.exists(_.name == idnuse.name) => PDestructorCall(idnuse.name, rcv)(pfa.pos)
      case pfa@PFieldAccess(rcv, idnuse) if declaredConstructorNames.exists("is" + _.name == idnuse.name) => PDiscriminatorCall(PIdnUse(idnuse.name.substring(2))(idnuse.pos), rcv)(pfa.pos)
    }).recurseFunc({
      // Stop the recursion if a destructor call or discriminator call is parsed as left-hand side of a field assignment
      case PFieldAssign(fieldAcc, _) if declaredConstructorArgsNames.exists(_.name == fieldAcc.idnuse.name) ||
        declaredConstructorNames.exists("is" + _.name == fieldAcc.idnuse.name) => Seq()
      case n: PNode => n.children collect {case ar: AnyRef => ar}
    }).execute(input)

    transformStrategy(input)
  }

  override def beforeVerify(input: Program): Program = {
    new AdtEncoder(input).encode()
  }

}

