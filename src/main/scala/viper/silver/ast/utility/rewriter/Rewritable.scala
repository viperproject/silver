// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter

import viper.silver.parser.{PDomain, PDomainFunction, PFields, PFunction, PMethod, PPredicate}
import viper.silver.parser.Transformer.ParseTreeDuplicationError
import viper.silver.ast.{AtomicType, BackendFuncApp, DomainFuncApp, ErrorTrafo, FuncApp, Info, Node, Position}

import scala.reflect.runtime.{universe => reflection}

/**
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable extends Product {

  def children: Seq[Any] = productIterator.toList

  def withChildren(children: Seq[Any], pos: Option[(Position, Position)] = None, forceRewrite: Boolean = false): this.type = {
    if (!forceRewrite && this.children == children && !pos.isDefined)
      this
    else {
      // Singleton objects shouldn't be rewritten, preserving their singularity
      if (this.isInstanceOf[AtomicType])
        this
      else {
        // Infer constructor from type
        val mirror = reflection.runtimeMirror(reflection.getClass.getClassLoader)
        val instanceMirror = mirror.reflect(this)
        val classSymbol = instanceMirror.symbol
        val classMirror = mirror.reflectClass(classSymbol)
        val constructorSymbol = instanceMirror.symbol.primaryConstructor.asMethod
        val constructorMirror = classMirror.reflectConstructor(constructorSymbol)

        // Add additional arguments to constructor call, besides children
        var firstArgList = children
        var secondArgList = Seq.empty[Any]
        import viper.silver.ast.{DomainType, DomainAxiom, FuncApp, DomainFunc, DomainFuncApp}
        import viper.silver.parser.{PAxiom, PMagicWandExp, PNode, PDomainType}
        this match {
          case dt: DomainType => secondArgList = Seq(dt.typeParameters)
          case da: DomainAxiom => secondArgList = Seq(da.pos, da.info, da.domainName, da.errT)
          case fa: FuncApp => secondArgList = Seq(fa.pos, fa.info, fa.typ, fa.errT)
          case df: DomainFunc => secondArgList = Seq(df.pos, df.info, df.domainName, df.errT)
          case df: DomainFuncApp => secondArgList = Seq(df.pos, df.info, df.typ, df.domainName, df.errT)
          case ba: BackendFuncApp => secondArgList = Seq(ba.pos, ba.info, ba.typ, ba.interpretation, ba.errT)
          case no: Node => secondArgList = no.getMetadata
          case pa: PAxiom => secondArgList = Seq(pa.domainName) ++ Seq(pos.getOrElse(pa.pos), pa.annotations)
          case pm: PMagicWandExp => firstArgList = Seq(children.head) ++ children.drop(2) ++ Seq(pos.getOrElse(pm.pos))
          case pd: PDomainFunction => secondArgList = Seq(pd.domainName) ++ Seq(pos.getOrElse(pd.pos), pd.annotations)
          case pd: PDomain => secondArgList = Seq(pos.getOrElse(pd.pos), pd.annotations)
          case pm: PMethod => secondArgList = Seq(pos.getOrElse(pm.pos), pm.annotations)
          case pp: PPredicate => secondArgList = Seq(pos.getOrElse(pp.pos), pp.annotations)
          case pf: PFunction => secondArgList = Seq(pos.getOrElse(pf.pos), pf.annotations)
          case pf: PFields => secondArgList = Seq(pos.getOrElse(pf.pos), pf.annotations)
          case pn: PNode => secondArgList = Seq(pos.getOrElse(pn.pos))
          case _ =>
        }

        // Call constructor
        val newNode = try {constructorMirror(firstArgList ++ secondArgList: _*)}
        catch {
          case _: Exception if (this.isInstanceOf[PNode]) =>
            throw ParseTreeDuplicationError(this.asInstanceOf[PNode], children)
        }

        // Copy member values, as they aren't in the parameters' list.
        this match {
          case dt: PDomainType =>
            newNode.asInstanceOf[PDomainType].kind = dt.kind
          case _ =>
        }

        newNode.asInstanceOf[this.type]
      }
    }
  }

  def meta: (Position, Info, ErrorTrafo) = {
    assert(this.isInstanceOf[Node], "Only descendants of class 'Node' have metadata")

    val metadata = this.asInstanceOf[Node].getMetadata
    (metadata(0).asInstanceOf[Position], metadata(1).asInstanceOf[Info], metadata(2).asInstanceOf[ErrorTrafo])
  }

  def withMeta(posInfoTrafo: (Position, Info, ErrorTrafo)): this.type = {
    assert(this.isInstanceOf[Node], "Only descendants of class 'Node' have metadata")

    val (pos, info, trafo) = posInfoTrafo

    // Singleton objects shouldn't be rewritten, preserving their singularity
    if (this.isInstanceOf[AtomicType])
      this
    else {
      // Infer constructor from type
      val mirror = reflection.runtimeMirror(reflection.getClass.getClassLoader)
      val instanceMirror = mirror.reflect(this)
      val classSymbol = instanceMirror.symbol
      val classMirror = mirror.reflectClass(classSymbol)
      val constructorSymbol = instanceMirror.symbol.primaryConstructor.asMethod
      val constructorMirror = classMirror.reflectConstructor(constructorSymbol)

      val arguments = this match {
        case fa: FuncApp => this.children ++ Seq(pos, info, fa.typ, trafo)
        case df: DomainFuncApp => this.children ++ Seq(pos, info, df.typ, df.domainName, trafo)
        case _ => this.children ++ Seq(pos, info, trafo)
      }

      // Call constructor
      val newNode = constructorMirror(arguments: _*)

      newNode.asInstanceOf[this.type]
    }
  }
}
