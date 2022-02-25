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
import viper.silver.parser.{PAnyFormalArgDecl, PDomainType, PFormalArgDecl, PFunction, PIdnDef, PIdnUse, PMethod, PNode, PProgram, PTypeVarDecl, ParserExtension}
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
    // Add new keyword
    ParserExtension.addNewKeywords(Set[String](AdtKeyword))
    // Add new declaration
    ParserExtension.addNewDeclAtEnd(adtDecl(_))
    // TODO: Add custom parsers
    input
  }

  override def beforeResolve(input: PProgram): PProgram = {
    // Replace PDomainType by PAdtType if a corresponding ADT exists, since they are automatically parsed as an PDomainType
    // and there is no way to extend the parser to avoid this.
    val declaredAdtNames = input.extensions.collect { case a: PAdt => a.idndef }.toSet
    // TODO: With the current strategy occurrences of PDomainTypes in constructor, function and method signatures
    //  are handled (especially they are converted to an PAdtType if there is an corresponding declaration).
    //  Handling of AdtTypes in variable declarations, built-in type declarations, etc. must be implemented in a later step.
    val newProgram: PProgram = StrategyBuilder.Slim[PNode]({
      case pa@PDomainType(idnuse, args) if declaredAdtNames.exists(_.name == idnuse.name) => PAdtType(idnuse, args)(pa.pos)
      case d => d
    }).recurseFunc({
      case PProgram(_, _, _, _, functions, _, methods, extensions, _) => Seq(extensions) ++ Seq(functions) ++ Seq(methods)
      case PMethod(_, formalArgs, formalReturns, _, _, _) => Seq(formalArgs) ++ Seq(formalReturns)
      case PFunction(_, formalArgs, typ, _, _, _) => Seq(formalArgs) ++ Seq(typ)
      case PAdt(_, _, constructors) => Seq(constructors)
      case PAdtConstructor(_, formalArgs) => Seq(formalArgs)
      case PFormalArgDecl(_, typ) => Seq(typ)
    }).execute(input)
    newProgram
  }

  override def beforeVerify(input: Program): Program = {
    // TODO: remove the following statement
    System.exit(-1)
    input
  }

}

