// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.ast._
import viper.silver.ast.pretty.FastPrettyPrinter.{ContOps, braces, brackets, char, defaultIndent, line, nest, nil, parens, show, showType, showVars, space, ssep, text}
import viper.silver.ast.pretty.PrettyPrintPrimitives
import viper.silver.ast.utility.Consistency
import viper.silver.verifier.{ConsistencyError, Failure, VerificationResult}

/**
  * This class represents a user-defined ADT.
  *
  * @param name         name of the ADT
  * @param constructors sequence of corresponding constructors
  * @param typVars      sequence of type variables (generics)
  * @param derivingInfo a map that maps identifiers of derivable functions to a tuple containing an optional type param and a set of excluded constructor argument identifiers
  */
case class Adt(name: String, constructors: Seq[AdtConstructor], typVars: Seq[TypeVar] = Nil, derivingInfo: Map[String, (Option[Type], Set[String])] = Map.empty)
              (val pos: Position = NoPosition, val info: Info = NoInfo, val errT: ErrorTrafo = NoTrafos) extends ExtensionMember {
  val scopedDecls: Seq[Declaration] = Seq()

  override def extensionSubnodes: Seq[Node] = constructors ++ typVars ++ derivingInfo.map(_._2._1).collect { case Some(v) => v }

  override lazy val check: Seq[ConsistencyError] = {
    if (constructors.isEmpty)
      Seq(ConsistencyError( s"ADT $name must have at least one constructor.", pos))
    else
      Seq()
  }

  override def prettyPrint: PrettyPrintPrimitives#Cont = {

    def showDerivingInfo(di: (String, (Option[Type], Set[String]))): PrettyPrintPrimitives#Cont = {
      val (func, (param, blocklist)) = di
      text(func) <> (if (param.isEmpty) nil else text("[") <> showType(param.get) <> space <> "]") <>
        space <> (if (blocklist.isEmpty) nil else text("without") <> space <> ssep(blocklist.toSeq map text, char(',') <> space))
    }

    text("adt") <+> name <>
      (if (typVars.isEmpty) nil else text("[") <> ssep(typVars map show, char(',') <> space) <> "]") <+>
      braces(nest(defaultIndent,
        line <> line <>
          ssep(constructors map show, line <> line)
      ) <> line) <+>
      (if (derivingInfo.isEmpty) nil else text("derives") <+>
        braces(nest(defaultIndent,
          line <> line <>
            ssep(derivingInfo.toSeq map showDerivingInfo, line <> line)
        ) <> line)
        )
  }
}

/**
  * This class represents an ADT constructor. See also the companion object below, which allows passing a
  * Adt - this should be used in general for creation (so that typ is guaranteed to
  * be set correctly)
  *
  * @param name       name of the ADT constructor
  * @param formalArgs sequence of arguments of the constructor
  * @param typ        the return type of the constructor
  * @param adtName    the name corresponding of the corresponding ADT
  */
case class AdtConstructor(name: String, formalArgs: Seq[LocalVarDecl])
                         (val pos: Position, val info: Info, val typ: AdtType, val adtName: String, val errT: ErrorTrafo)
  extends ExtensionMember {

  val scopedDecls: Seq[Declaration] = formalArgs

  override def getMetadata: Seq[Any] = {
    Seq(pos, info, errT)
  }

  override def extensionSubnodes: Seq[Node] = formalArgs

  override def prettyPrint: PrettyPrintPrimitives#Cont = text(name) <> parens(showVars(formalArgs))

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)], forceRewrite: Boolean): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 2, s"AdtConstructor : expected length 2 but got ${children.length}")
      val first = children.head.asInstanceOf[String]
      val second = children.tail.head.asInstanceOf[Seq[LocalVarDecl]]
      AdtConstructor(first, second)(this.pos, this.info, this.typ, this.adtName, this.errT).asInstanceOf[this.type]
    }

  }
}

object AdtConstructor {
  def apply(adt: Adt, name: String, formalArgs: Seq[LocalVarDecl])
           (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): AdtConstructor = {
    AdtConstructor(name, formalArgs)(pos, info, AdtType(adt, (adt.typVars zip adt.typVars).toMap), adt.name, errT)
  }
}

/**
  * This class represents an user-defined ADT type. See also the companion object below, which allows passing a
  * Adt - this should be used in general for creation (so that typeParameters is guaranteed to
  * be set correctly)
  *
  * @param adtName           The name of the underlying adt.
  * @param partialTypVarsMap Maps type parameters to (possibly concrete) types. May not map all
  *                          type parameters, may even be empty.
  * @param typeParameters    The type variables of the ADT type.
  */
case class AdtType(adtName: String, partialTypVarsMap: Map[TypeVar, Type])
                  (val typeParameters: Seq[TypeVar]) extends ExtensionType {

  override lazy val check: Seq[ConsistencyError] = if (!(typeParameters.toSet == typVarsMap.keys.toSet)) {
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
    assert(typVarsMap.keys.toSet equals this.typeParameters.toSet)
    val newTypeMap = typVarsMap.map(kv => kv._1 -> kv._2.substitute(newTypVarsMap))
    AdtType(adtName, newTypeMap)(typeParameters)
  }

  /** Is this a concrete type (i.e. no uninstantiated type variables)? */
  override def isConcrete: Boolean = typVarsMap.values.forall(_.isConcrete)

  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    val typArgs = typeParameters map (t => show(typVarsMap.getOrElse(t, t)))
    text(adtName) <> (if (typArgs.isEmpty) nil else brackets(ssep(typArgs, char(',') <> space)))
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

object AdtType {
  def apply(adt: Adt, typVarsMap: Map[TypeVar, Type]): AdtType =
    AdtType(adt.name, typVarsMap)(adt.typVars)
}


/**
  * This class represents a user-defined adt constructor application. See also the companion object below, which allows passing a
  * Adt constructor - this should be used in general for creation (so that typ is guaranteed to
  * be set correctly)
  *
  * @param name      The name of the ADT constructor
  * @param args      A sequence of expressions passed as arguments to the constructor
  * @param typVarMap Maps type parameters to (possibly concrete) types. May not map all
  *                  type parameters, may even be empty.
  * @param typ       The return type of the constructor
  * @param adtName   The corresponding ADT name
  */
case class AdtConstructorApp(name: String, args: Seq[Exp], typVarMap: Map[TypeVar, Type])
                            (val pos: Position, val info: Info, override val typ: Type, val adtName: String, val errT: ErrorTrafo)
  extends ExtensionExp {
  override lazy val check: Seq[ConsistencyError] = args.flatMap(Consistency.checkPure)

  override def prettyPrint: PrettyPrintPrimitives#Cont = {
    if (typVarMap.nonEmpty)
      // Type may be under-constrained, so to be safe we explicitly print out the type.
      parens(text(name) <> parens(ssep(args map show, char(',') <> space)) <> char(':') <+> show(typ))
    else
      text(name) <> parens(ssep(args map show, char(',') <> space))
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
  def apply(constructor: AdtConstructor, args: Seq[Exp], typVarMap: Map[TypeVar, Type])
           (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): AdtConstructorApp =
    AdtConstructorApp(constructor.name, args, typVarMap)(pos, info, constructor.typ.substitute(typVarMap), constructor.adtName, errT)
}

/**
  * This class represents an adt destructor application. See also the companion object below, which allows passing a
  * Adt - this should be used in general for creation (so that typ is guaranteed to
  * be set correctly)
  *
  * @param name      The name of the argument of an ADT constructor the destructor corresponds to
  * @param rcv       An expression on with the the destructor is applied
  * @param typVarMap Maps type parameters to (possibly concrete) types. May not map all
  *                  type parameters, may even be empty.
  * @param typ       The return type of the destructor
  * @param adtName   The corresponding ADT name
  */
case class AdtDestructorApp(name: String, rcv: Exp, typVarMap: Map[TypeVar, Type])
                           (val pos: Position, val info: Info, override val typ: Type, val adtName: String, val errT: ErrorTrafo) extends ExtensionExp {

  override lazy val check: Seq[ConsistencyError] = Consistency.checkPure(rcv)

  override def prettyPrint: PrettyPrintPrimitives#Cont = show(rcv) <> "." <> name

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq(rcv) ++ typVarMap.keys ++ typVarMap.values

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "AdtDestructorApp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("AdtDestructorApp: verifyExtExp has not been implemented.", pos)))
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)], forceRewrite: Boolean): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 3, s"AdtDestructorApp : expected length 3 but got ${children.length}")
      val first = children.head.asInstanceOf[String]
      val second = children(1).asInstanceOf[Exp]
      val third = children(2).asInstanceOf[Map[TypeVar, Type]]
      AdtDestructorApp(first, second, third)(this.pos, this.info, this.typ, this.adtName, this.errT).asInstanceOf[this.type]
    }
  }
}

object AdtDestructorApp {
  def apply(adt: Adt, name: String, rcv: Exp, typVarMap: Map[TypeVar, Type])
           (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): AdtDestructorApp = {
    val matchingConstructors = adt.constructors flatMap (c => c.formalArgs.filter { lv => lv.name == name })
    assert(matchingConstructors.length == 1, s"AdtDestructorApp : expected length 1 but got ${matchingConstructors.length}")
    val typ = matchingConstructors.head.typ
    AdtDestructorApp(name, rcv, typVarMap)(pos, info, typ.substitute(typVarMap), adt.name, errT)
  }
}

/**
  * This class represents an adt discriminator application. See also the companion object below, which allows passing a
  * Adt - this should be used in general for creation (so that adtName is guaranteed to
  * be set correctly)
  *
  * @param name      The name of the argument of an ADT constructor the destructor corresponds to
  * @param rcv       An expression on with the the destructor is applied
  * @param typVarMap Maps type parameters to (possibly concrete) types. May not map all
  *                  type parameters, may even be empty.
  * @param adtName   The corresponding ADT name
  */
case class AdtDiscriminatorApp(name: String, rcv: Exp, typVarMap: Map[TypeVar, Type])
                              (val pos: Position, val info: Info, val adtName: String, val errT: ErrorTrafo) extends ExtensionExp {

  override lazy val check: Seq[ConsistencyError] = Consistency.checkPure(rcv)

  override def typ: Type = Bool

  override def prettyPrint: PrettyPrintPrimitives#Cont = show(rcv) <> "." <> name <> "?"

  override def extensionIsPure: Boolean = true

  override def extensionSubnodes: Seq[Node] = Seq(rcv) ++ typVarMap.keys ++ typVarMap.values

  override def verifyExtExp(): VerificationResult = {
    assert(assertion = false, "AdtDiscriminatorApp: verifyExtExp has not been implemented.")
    Failure(Seq(ConsistencyError("AdtDiscriminatorApp: verifyExtExp has not been implemented.", pos)))
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)], forceRewrite: Boolean): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 3, s"AdtDestructorApp : expected length 3 but got ${children.length}")
      val first = children.head.asInstanceOf[String]
      val second = children(1).asInstanceOf[Exp]
      val third = children(2).asInstanceOf[Map[TypeVar, Type]]
      AdtDiscriminatorApp(first, second, third)(this.pos, this.info, this.adtName, this.errT).asInstanceOf[this.type]
    }
  }

}

object AdtDiscriminatorApp {
  def apply(adt: Adt, name: String, rcv: Exp, typVarMap: Map[TypeVar, Type])
           (pos: Position = NoPosition, info: Info = NoInfo, errT: ErrorTrafo = NoTrafos): AdtDiscriminatorApp = {
    AdtDiscriminatorApp(name, rcv, typVarMap)(pos, info, adt.name, errT)
  }
}

