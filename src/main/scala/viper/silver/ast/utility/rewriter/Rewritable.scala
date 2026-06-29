// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility.rewriter

import viper.silver.parser.PNode
import viper.silver.ast.{AtomicType, BackendFuncApp, DomainFuncApp, ErrorTrafo, FuncApp, Info, Node, Position}

import scala.reflect.runtime.{universe => reflection}

trait HasExtraValList {
  def getExtraVals: Seq[Any]
}
trait HasExtraVars {
  def copyExtraVars(from: Any): Unit
}

/**
  * Trait Rewritable provides an interface that specifies which methods are required for the rewriter to work with.
  * For classes that implement product (especially case classes) everything is already implemented here and one only has to extend this base class
  */
trait Rewritable extends Product {

  lazy val children: Seq[Any] = productIterator.toSeq

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
        val firstArgList = children
        var secondArgList = Seq.empty[Any]
        import viper.silver.ast.{DomainType, DomainAxiom, FuncApp, DomainFunc, DomainFuncApp}
        this match {
          // TODO: remove the following cases by implementing `HasExtraValList` on the respective classes
          case dt: DomainType => secondArgList = Seq(dt.typeParameters)
          case da: DomainAxiom => secondArgList = Seq(da.pos, da.info, da.domainName, da.errT)
          case fa: FuncApp => secondArgList = Seq(fa.pos, fa.info, fa.typ, fa.errT)
          case df: DomainFunc => secondArgList = Seq(df.pos, df.info, df.domainName, df.errT)
          case df: DomainFuncApp => secondArgList = Seq(df.pos, df.info, df.typ, df.domainName, df.errT)
          case ba: BackendFuncApp => secondArgList = Seq(ba.pos, ba.info, ba.typ, ba.interpretation, ba.errT)
          case no: Node => secondArgList = no.getMetadata

          case evl: HasExtraValList => {
            secondArgList = evl.getExtraVals.map(ev => {
              // Replace positions with the new one
              val replace = pos.isDefined && ev.isInstanceOf[(_, _)] && ev.asInstanceOf[(_, _)]._1.isInstanceOf[Position] && ev.asInstanceOf[(_, _)]._2.isInstanceOf[Position]
              if (replace) pos.get else ev
            })
          }
          case _ =>
        }

        // Call constructor
        val newNode = try {constructorMirror(firstArgList ++ secondArgList: _*)}
        catch {
          case _: Exception if (this.isInstanceOf[PNode]) =>
            throw ParseTreeDuplicationError(this.asInstanceOf[PNode], children)
        }

        // Copy member values, as they aren't in the parameters' list.
        newNode match {
          case ev: HasExtraVars =>
            ev.copyExtraVars(this)
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

  def initProperties(): Unit = ()
}

case class ParseTreeDuplicationError(original: PNode, newChildren: Seq[Any])
    extends RuntimeException(s"Cannot duplicate $original with new children $newChildren")
