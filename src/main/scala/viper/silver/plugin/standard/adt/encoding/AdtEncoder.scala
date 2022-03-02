// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt.encoding

import viper.silver.ast.utility.rewriter.StrategyBuilder
import viper.silver.ast._
import viper.silver.plugin.standard.adt.{Adt, AdtConstructor, AdtType}




class AdtEncoder (val program: Program) {

  /**
    * This method encodes all ADT related AST nodes to normal AST nodes.
    *
    * @return
    */
  def encode(): Program = {

    // In a first step encode all adt top level declarations
    val encodedAdts: Seq[Domain] = program.extensions map {case a: Adt => encodeAdtAsDomain(a)}
    val newProgram: Program = program.copy(domains = program.domains ++ encodedAdts, extensions = Seq())(program.pos, program.info, program.errT)

    // In a second step encode all occurrences of AdtType's as DomainType's
    encodeAllAdtTypeAsDomainType(newProgram)
  }

  /**
    * This method takes an ADT and encodes it as a Domain
    *
    * @param adt the ADT to encode
    * @return an the encoded ADT as a domain
    */
  private def encodeAdtAsDomain(adt: Adt): Domain = {
    adt match {
      case Adt(name, constructors, typVars) =>
        val domain = Domain(name, null, null, typVars)(adt.pos, adt.info, adt.errT)
        // TODO: Add injectivity, exclusivity, destructors, etc.
        val functions = constructors map encodeAdtConstructorAsDomainFunc(domain)
        val axioms = Seq()
        domain.copy(functions = functions, axioms = axioms)(adt.pos, adt.info, adt.errT)
    }
  }

  /**
    * This method encodes an ADT constructor as a domain function
    *
    * @param domain the domain the encoded constructor belongs to
    * @param ac the ADT constructor to encode
    * @return an encoded ADT constructor as a domain function
    */
  private def encodeAdtConstructorAsDomainFunc(domain: Domain)(ac: AdtConstructor): DomainFunc = {
    ac match {
      case a@AdtConstructor(name, formalArgs) => DomainFunc(name, formalArgs, DomainType(domain, Map.empty))(a.pos, a.info, domain.name, a.errT)
    }
  }

  /**
    * This method traverses the entire AST an encodes any occurrences of an AdtType as a DomainType
    *
    * @param program The program to encode
    * @return a program free of AdtType's
    */
  private def encodeAllAdtTypeAsDomainType(program: Program): Program = {
    StrategyBuilder.Slim[Node]({
      case at@AdtType(adtName, partialTypVarsMap) => DomainType(adtName, partialTypVarsMap)(at.typeParameters)
    }).recurseFunc({
      case fa@FuncApp(_, args) => Seq(args, fa.typ)
      case df@DomainFuncApp(_, args, typVarMap) => Seq(args, typVarMap, df.typ)
      case d: Node => d.children.collect {case ar: AnyRef => ar}
    }).execute(program)
  }

}
