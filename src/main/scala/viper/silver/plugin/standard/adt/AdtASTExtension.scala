// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, braces, brackets, char, defaultIndent, line, nest, nil, parens, show, showVars, space, ssep, text}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.Consistency
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}

/**
  * This class represents a user-defined ADT.
  *
  * @param name name of the ADT
  * @param constructors sequence of corresponding constructors
  * @param typVars sequence of type variables (generics)
  */
case class Adt(name: String, constructors: Seq[AdtConstructor], typVars: Seq[TypeVar] = Nil)
                 (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionMember {
  val scopedDecls: Seq[Declaration] = Seq()

  override def extensionSubnodes: Seq[Node] = constructors ++ typVars

  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    text("adt") <+> name <>
      (if (typVars.isEmpty) nil else text("[") <> ssep(typVars map show, char (',') <> space) <> "]") <+>
      braces(nest(defaultIndent,
        line <> line <>
          ssep(constructors map show, line <> line)
      ) <> line)
  }
}

/**
  * This class represents an ADT constructor. See also the companion object below, which allows passing a
  * Adt - this should be used in general for creation (so that typ is guaranteed to
  * be set correctly)
  *
  * @param name name of the ADT constructor
  * @param formalArgs sequence of arguments of the constructor
  * @param typ the return type of the constructor
  * @param adtName the name corresponding of the corresponding ADT
  */
case class AdtConstructor(name: String, formalArgs: Seq[AnyLocalVarDecl])
                     (val pos: Position, val info: Info, val typ: AdtType, val adtName : String, val errT: ErrorTrafo)
  extends ExtensionMember {

  override def getMetadata:Seq[Any] = {
    Seq(pos, info, errT)
  }
  val scopedDecls: Seq[Declaration] = formalArgs.filter(p => p.isInstanceOf[LocalVarDecl]).asInstanceOf[Seq[LocalVarDecl]]

  override def extensionSubnodes: Seq[Node] = formalArgs

  override def prettyPrint: PrettyPrintPrimitives#Cont = text(name) <> parens(showVars(formalArgs))

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)], forceRewrite: Boolean): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 2, s"AdtConstructor : expected length 2 but got ${children.length}")
      val first = children.head.asInstanceOf[String]
      val second = children.tail.head.asInstanceOf[Seq[AnyLocalVarDecl]]
      AdtConstructor(first, second)(this.pos, this.info, this.typ, this.adtName, this.errT).asInstanceOf[this.type]
    }

  }
}

object AdtConstructor {
  def apply(adt: Adt, name: String, formalArgs: Seq[AnyLocalVarDecl])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): AdtConstructor = {
    AdtConstructor(name, formalArgs)(pos, info, AdtType(adt, (adt.typVars zip adt.typVars).toMap), adt.name, errT)
  }
}

/**
  * This class represents an user-defined ADT type. See also the companion object below, which allows passing a
  * Adt - this should be used in general for creation (so that typeParameters is guaranteed to
  * be set correctly)
  *
  * @param adtName The name of the underlying adt.
  * @param partialTypVarsMap Maps type parameters to (possibly concrete) types. May not map all
  *                          type parameters, may even be empty.
  * @param typeParameters The type variables of the ADT type.
  */
case class AdtType(adtName: String, partialTypVarsMap: Map[TypeVar, Type])
                  (val typeParameters: Seq[TypeVar]) extends ExtensionType {

  override lazy val check: Seq[ConsistencyError] = if(!(typeParameters.toSet == typVarsMap.keys.toSet)) {
    Seq(ConsistencyError(s"${typeParameters.toSet} doesn't equal ${typVarsMap.keys.toSet}", NoPosition))
  } else Seq()

  /**
    * Map each type parameter `A` to `partialTypVarsMap(A)`, if defined, otherwise to `A` itself.
    * `typVarsMap` thus contains a mapping for each type parameter.
    */
  val typVarsMap: Map[TypeVar, Type] =
    typeParameters.map(tp => tp -> partialTypVarsMap.getOrElse(tp, tp)).to(implicitly)

  /**
    * Takes a mapping of type variables to types and substitutes all
    * occurrences of those type variables with the corresponding type.
    */
  override def substitute(newTypVarsMap: Map[TypeVar, Type]): Type = {
    assert (typVarsMap.keys.toSet equals this.typeParameters.toSet)
    val newTypeMap = typVarsMap.map(kv=>kv._1 -> kv._2.substitute(newTypVarsMap))
    AdtType(adtName, newTypeMap)(typeParameters)
  }

  /** Is this a concrete type (i.e. no uninstantiated type variables)? */
  override def isConcrete: Boolean = typVarsMap.values.forall(_.isConcrete)

  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    val typArgs = typeParameters map (t => show(typVarsMap.getOrElse(t, t)))
    text(adtName) <> (if (typArgs.isEmpty) nil else brackets(ssep(typArgs, char (',') <> space)))
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)], forceRewrite: Boolean): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 2, s"AdtType : expected length 2 but got ${children.length}")
      val first = children.head.asInstanceOf[String]
      val second = children.tail.head.asInstanceOf[Map[TypeVar, Type]]
      AdtType(first, second)(this.typeParameters).asInstanceOf[this.type]
    }
  }

}

object AdtType{
  def apply(adt: Adt, typVarsMap: Map[TypeVar, Type]): AdtType =
    AdtType(adt.name, typVarsMap)(adt.typVars)
}


/**
  * This class represents a user-defined adt constructor application. See also the companion object below, which allows passing a
  * Adt constructor - this should be used in general for creation (so that typ is guaranteed to
  * be set correctly)
  *
  * @param name The name of the ADT constructor
  * @param args A sequence of expressions passed as arguments to the constructor
  * @param typVarMap Maps type parameters to (possibly concrete) types. May not map all
  *                  type parameters, may even be empty.
  * @param typ The return type of the constructor
  * @param adtName The corresponding ADT name
  */
case class AdtConstructorApp(name: String, args: Seq[Exp], typVarMap: Map[TypeVar, Type])
                        (val pos: Position, val info: Info, override val typ: Type, val adtName:String, val errT: ErrorTrafo)
  extends ExtensionExp {
  override lazy val check : Seq[ConsistencyError] = args.flatMap(Consistency.checkPure)

  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    if (typVarMap.nonEmpty)
      // Type may be under-constrained, so to be safe we explicitly print out the type.
      parens(text(name) <> parens(ssep(args map show, char (',') <> space)) <> char(':') <+> show(typ))
    else
      text(name) <> parens(ssep(args map show, char (',') <> space))
  }

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = args ++ typVarMap.keys ++ typVarMap.values

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "AdtConstructorApp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("AdtConstructorApp: verifyExtExp has not been implemented.", pos)))
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)], forceRewrite: Boolean): AdtConstructorApp.this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 3, s"AdtConstructorApp : expected length 3 but got ${children.length}")
      val first = children.head.asInstanceOf[String]
      val second = children(1).asInstanceOf[Seq[Exp]]
      val third = children(2).asInstanceOf[Map[TypeVar, Type]]
      AdtConstructorApp(first, second, third)(this.pos, this.info, this.typ, this.adtName, this.errT).asInstanceOf[this.type]
    }
  }
}
object AdtConstructorApp {
  def apply(constructor : AdtConstructor, args: Seq[Exp], typVarMap: Map[TypeVar, Type])(pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos) : AdtConstructorApp =
    AdtConstructorApp(constructor.name, args, typVarMap)(pos, info, constructor.typ.substitute(typVarMap), constructor.adtName, errT)
}


