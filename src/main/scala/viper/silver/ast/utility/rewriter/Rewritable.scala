// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter

import viper.silver.FastPositions
import viper.silver.parser.{FastPositioned, PDomainFunction}
import viper.silver.parser.Transformer.ParseTreeDuplicationError
import scala.reflect.runtime.{universe => reflection}

/**
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable extends Product {

  def children: Seq[Any] = productIterator.toList

  def children_= (children: Seq[Any]): this.type = {
    if (this.children == children)
      this
    else {
      // Singleton objects shouldn't be rewritten, preserving their singularity
      if (this.isInstanceOf[viper.silver.ast.AtomicType])
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
        import viper.silver.ast.{Node, DomainType, DomainAxiom, FuncApp, DomainFunc, DomainFuncApp}
        import viper.silver.parser.{PAxiom, PMagicWandExp, PNode, PDomainType}
        this match {
          case dt: DomainType => secondArgList = Seq(dt.typeParameters)
          case da: DomainAxiom => secondArgList = Seq(da.pos, da.info, da.domainName, da.errT)
          case fa: FuncApp => secondArgList = Seq(fa.pos, fa.info, fa.typ, fa.errT)
          case df: DomainFunc => secondArgList = Seq(df.pos, df.info, df.domainName, df.errT)
          case df: DomainFuncApp => secondArgList = Seq(df.pos, df.info, df.typ, df.domainName, df.errT)
          case no: Node => secondArgList = no.getMetadata
          case pa: PAxiom => secondArgList = Seq(pa.domainName)
          case _: PMagicWandExp => firstArgList = Seq(children.head) ++ children.drop(2)
          case pd: PDomainFunction => secondArgList = Seq(pd.domainName)
          case _ =>
        }

        // Call constructor
        val newNode = try {constructorMirror(firstArgList ++ secondArgList: _*)}
        catch {
          case _: Exception if (this.isInstanceOf[PNode]) =>
            throw ParseTreeDuplicationError(this.asInstanceOf[PNode], children)
        }

        // Copy position information for PNodes, as they are stored outside of the AST
        this match {
          case fp: FastPositioned =>
            FastPositions.setStart(newNode, FastPositions.getStart(fp))
            FastPositions.setFinish(newNode, FastPositions.getFinish(fp))
          case _ =>
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
}
