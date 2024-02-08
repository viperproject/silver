// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2022 ETH Zurich.

package viper.silver.plugin.standard.adt

import viper.silver.FastMessaging
import viper.silver.ast._
import viper.silver.parser._
import viper.silver.plugin.standard.adt.PAdtConstructor.findAdtConstructor

import scala.annotation.unused
import viper.silver.ast.utility.rewriter.HasExtraVars

/**
  * Keywords used to define ADT's
  */
case object PAdtKeyword extends PKw("adt") with PKeywordLang
case object PDerivesKeyword extends PKw("derives") with PKeywordLang
case object PWithoutKeyword extends PKw("without") with PKeywordLang

case class PAdt(annotations: Seq[PAnnotation], adt: PReserved[PAdtKeyword.type], idndef: PIdnDef, typVars: Option[PDelimited.Comma[PSym.Bracket, PTypeVarDecl]], c: PAdtSeq[PAdtConstructor], derive: Option[PAdtDeriving])
               (val pos: (Position, Position)) extends PExtender with PSingleMember with PGlobalDeclaration with PPrettySubnodes {
  def typVarsSeq: Seq[PTypeVarDecl] = typVars.map(_.inner.toSeq).getOrElse(Nil)
  def constructors: Seq[PAdtConstructor] = c.inner

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      constructors foreach (_.typecheck(t, n))
      derive foreach (_.typecheck(t, n))
    }
    None
  }

  override def translateMemberSignature(t: Translator): Adt = {

    Adt(
      idndef.name,
      null,
      typVarsSeq map (t => TypeVar(t.idndef.name)),
      derive.toSeq.flatMap(_.derivingInfos.inner.map { a =>
        val without = a.without.toSet
        (a.idndef.name, (if (a.param.nonEmpty) Some(t.ttyp(a.param.get.inner)) else None, without.flatMap(_.blockList.toSeq.map(_.name))))
      }).toMap
    )(t.liftPos(this), Translator.toInfo(this.annotations, this))
  }

  override def translateMember(t: Translator): Member = {

    // In a first step translate constructor signatures
    constructors map (c => {
      val cc = c.translateMemberSignature(t)
      t.getMembers().put(c.idndef.name, cc)
    })

    val a = PAdt.findAdt(idndef, t)
    val aa = a.copy(constructors = constructors map (_.translateMember(t)))(a.pos, a.info, a.errT)
    t.getMembers()(a.name) = aa
    aa
  }

  /**
    * This is a helper method that creates an AdtType from the ADT's signature.
    *
    * @return An AdtType that corresponds to the ADTs signature
    */
  def getAdtType: PAdtType = {
    val adtType = PAdtType(PIdnRef(idndef.name)(NoPosition, NoPosition), typVars map (tv => tv.update(tv.inner.toSeq map { t =>
      val typeVar = PDomainType(PIdnRef(t.idndef.name)(NoPosition, NoPosition), None)(NoPosition, NoPosition)
      typeVar.kind = PDomainTypeKinds.TypeVar
      typeVar
    })))(NoPosition, NoPosition)
    adtType.adt.newDecl(this)
    adtType.kind = PAdtTypeKinds.Adt
    adtType
  }
}

object PAdt {
  /**
    * This is a helper method helper that can be called if one knows which 'id' refers to an ADT
    *
    * @param id identifier of the ADT
    * @param t  translator unit
    * @return the corresponding ADT object
    */
  def findAdt(id: PIdentifier, t: Translator): Adt = t.getMembers()(id.name).asInstanceOf[Adt]

}

trait PAdtChild extends PNode {
  def adt: PAdt = getAncestor[PAdt].get
}

case class PAdtSeq[T <: PNode](seq: PGrouped[PSym.Brace, Seq[T]])(val pos: (Position, Position)) extends PExtender {
  def inner: Seq[T] = seq.inner
  override def pretty = s"${seq.l.pretty}\n  ${seq.inner.map(_.pretty).mkString("\n  ")}\n${seq.r.pretty}"
}

/** Any argument to a method, function or predicate. */
case class PAdtFieldDecl(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl with PTypedDeclaration with PGlobalDeclaration with PMemberUniqueDeclaration with PAdtChild {
  def constructor: PAdtConstructor = getAncestor[PAdtConstructor].get
  def annotations: Seq[PAnnotation] = Nil
}
object PAdtFieldDecl {
  def apply(d: PIdnTypeBinding): PAdtFieldDecl = PAdtFieldDecl(d.idndef, d.c, d.typ)(d.pos)
}

case class PAdtConstructor(annotations: Seq[PAnnotation], idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PAdtFieldDecl])(val pos: (Position, Position)) extends PExtender with PNoSpecsFunction with PGlobalUniqueDeclaration with PPrettySubnodes with PAdtChild {
  override def resultType: PType = adt.getAdtType
  def fieldDecls: Seq[PAdtFieldDecl] = this.args.inner.toSeq
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this.formalArgs foreach (a => t.check(a.typ))
    // Check if there are name clashes for the corresponding discriminator, if so we raise a type-check error
    val discClashes = t.names.globalDefinitions("is" + idndef.name)
    if (discClashes.nonEmpty) {
      val decl = discClashes.head
      t.messages ++= FastMessaging.message(idndef, "corresponding adt discriminator identifier `" + decl.idndef.name + "` at " + idndef.pos._1 + " is shadowed at " + decl.idndef.pos._1)
    }
    None
  }

  override def translateMemberSignature(t: Translator): AdtConstructor = {
    AdtConstructor(
      PAdt.findAdt(adt.idndef, t),
      idndef.name,
      formalArgs map (_.asInstanceOf[PAdtFieldDecl]) map { arg => LocalVarDecl(arg.idndef.name, t.ttyp(arg.typ))(t.liftPos(arg.idndef)) }
    )(t.liftPos(this), Translator.toInfo(annotations, this))
  }

  override def translateMember(t: Translator): AdtConstructor = {
    findAdtConstructor(idndef, t)
  }

  override def keyword = adt.adt
  override def c = PReserved.implied(PSym.Colon)
  override def body = None
}

object PAdtConstructor {
  /**
    * This is a helper method helper that can be called if one knows which 'id' refers to an ADTConstructor
    *
    * @param id identifier of the ADT constructor
    * @param t  translator unit
    * @return the corresponding ADTConstructor object
    */
  def findAdtConstructor(id: PIdentifier, t: Translator): AdtConstructor = t.getMembers()(id.name).asInstanceOf[AdtConstructor]
}

case class PAdtConstructors1(seq: PGrouped[PSym.Brace, Seq[PAdtConstructor1]])(val pos: (Position, Position))
case class PAdtConstructor1(annotations: Seq[PAnnotation], idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PAdtFieldDecl], s: Option[PSym.Semi])(val pos: (Position, Position))

case class PAdtDeriving(k: PReserved[PDerivesKeyword.type], derivingInfos: PAdtSeq[PAdtDerivingInfo])(val pos: (Position, Position)) extends PExtender with PPrettySubnodes with PAdtChild {
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    derivingInfos.inner foreach (_.typecheck(t, n))

    // Check duplicate deriving infos
    val duplicateDerivingInfo = derivingInfos.inner.groupBy(_.idndef.name).collect { case (_, ys) if ys.size > 1 => ys.head }
    t.messages ++= duplicateDerivingInfo.flatMap { di =>
      FastMessaging.message(di.idndef, s"duplicate derivation of function `${di.idndef.name}`")
    }

    None
  }
}

case class PAdtWithout(k: PReserved[PWithoutKeyword.type], blockList: PDelimited[PIdnRef[PAdtFieldDecl], PSym.Comma])(val pos: (Position, Position)) extends PExtender with PPrettySubnodes with PAdtChild {
  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    blockList.toSeq.foreach(idnref => {
      if (idnref.filterDecls(_.constructor.adt.scopeId == adt.scopeId))
        t.messages ++= FastMessaging.message(idnref, s"undeclared adt field `${idnref.name}`, expected field in containing adt")
      else if (idnref.decl.isEmpty)
        t.messages ++= FastMessaging.message(idnref, s"ambiguous adt field `${idnref.name}`")
    })
    None
  }
}

case class PAdtDerivingInfo(idndef: PIdnDef, param: Option[PGrouped[PSym.Bracket, PType]], without: Option[PAdtWithout])(val pos: (Position, Position)) extends PExtender with PPrettySubnodes {

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    param.map(_.inner) foreach (t.check)
    without map (_.typecheck(t, n))
    None
  }
}

case class PAdtType(adt: PIdnRef[PAdt], args: Option[PDelimited.Comma[PSym.Bracket, PType]])
                   (val pos: (Position, Position)) extends PExtender with PGenericType with HasExtraVars {

  var kind: PAdtTypeKinds.Kind = PAdtTypeKinds.Unresolved

  def typeArgs = args.map(_.inner.toSeq).getOrElse(Nil)
  override def genericName: String = adt.name
  override def typeArguments: Seq[PType] = typeArgs
  override def isValidOrUndeclared: Boolean = (kind == PAdtTypeKinds.Adt || isUndeclared) && typeArgs.forall(_.isValidOrUndeclared)

  override def substitute(ts: PTypeSubstitution): PType = {
    require(kind == PAdtTypeKinds.Adt || isUndeclared)
    val oldArgs = typeArgs
    val newArgs = oldArgs map (a => a.substitute(ts))
    if (oldArgs == newArgs)
      return this

    val newAdtType = PAdtType(adt, args.map(a => a.update(newArgs)))((NoPosition, NoPosition))
    newAdtType.kind = PAdtTypeKinds.Adt
    newAdtType
  }

  def isUndeclared: Boolean = kind == PAdtTypeKinds.Undeclared

  override def subNodes: Seq[PType] = typeArgs

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this match {
      case at@PAdtType(_, _) if at.isResolved => None
      /* Already resolved, nothing left to do */
      case at@PAdtType(adt, args) =>
        assert(!at.isResolved, "Only yet-unresolved adt types should be type-checked and resolved")

        typeArgs foreach t.check

        at.kind = PAdtTypeKinds.Undeclared

        if (adt.decls.isEmpty)
          Some(Seq(s"undeclared type `${at.adt.name}`, expected adt"))
        else if (adt.decl.isEmpty)
          Some(Seq(s"ambiguous adt type `${at.adt.name}`"))
        else {
          at.kind = PAdtTypeKinds.Adt
          val x: PAdt = adt.decl.get.asInstanceOf[PAdt]
          t.ensure(args.map(_.inner.length) == x.typVars.map(_.inner.length), this, "wrong number of type arguments")
          None
        }
    }
  }

  def isResolved: Boolean = kind != PAdtTypeKinds.Unresolved

  override def translateType(t: Translator): Type = {
    t.getMembers().get(adt.name) match {
      case Some(d) =>
        val adt = d.asInstanceOf[Adt]
        val typVarMapping = adt.typVars zip (typeArgs map t.ttyp)
        AdtType(adt, typVarMapping.toMap)
      case None => sys.error("undeclared adt type")
    }
  }

  override def withTypeArguments(s: Seq[PType]): PAdtType =
    if (s.length == 0 && args.isEmpty) this else copy(args = Some(args.get.update(s)))(pos)
  override def copyExtraVars(from: Any): Unit = this.kind = from.asInstanceOf[PAdtType].kind
}

object PAdtTypeKinds {
  trait Kind

  case object Unresolved extends Kind

  case object Adt extends Kind

  case object Undeclared extends Kind
}

/** Common trait for ADT operator applications * */
sealed trait PAdtOpApp extends PExtender with POpApp {
  // Following fields are set during resolving, respectively in the typecheck method below
  var adtTypeRenaming: Option[PTypeRenaming] = None
  var adtSubstitution: Option[PTypeSubstitution] = None
  var _extraLocalTypeVariables: Set[PDomainType] = Set()

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = PAdtOpApp.typecheck(this)(t, n)

  override def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = {
    t.checkTopTyped(this, Some(expected))
    None
  }

  override def forceSubstitution(ots: PTypeSubstitution): Unit = {
    val ts = adtTypeRenaming match {
      case Some(dtr) =>
        val s3 = PTypeSubstitution(dtr.mm.map(kv => kv._1 -> (ots.get(kv._2) match {
          case Some(pt) => pt
          case None => PTypeSubstitution.defaultType
        })))
        assert(s3.m.keySet == dtr.mm.keySet)
        assert(s3.m.forall(_._2.isGround))
        adtSubstitution = Some(s3)
        dtr.mm.values.foldLeft(ots)(
          (tss, s) => if (tss.contains(s)) tss else tss.add(s, PTypeSubstitution.defaultType).toOption.get)
      case _ => ots
    }
    super.forceSubstitution(ts)
  }

  override def extraLocalTypeVariables: Set[PDomainType] = _extraLocalTypeVariables

}

object PAdtOpApp {
  /**
    * This method mirrors the functionality in Resolver.scala that handles operation applications, except that it is
    * adapted to work for ADT operator applications.
    */
  def typecheck(poa: PAdtOpApp)(t: TypeChecker, @unused n: NameAnalyser): Option[Seq[String]] = {

    def getFreshTypeSubstitution(tvs: Seq[PDomainType]): PTypeRenaming =
      PTypeVar.freshTypeSubstitutionPTVs(tvs)

    // Checks that a substitution is fully reduced (idempotent)
    def refreshWith(ts: PTypeSubstitution, rts: PTypeRenaming): PTypeSubstitution = {
      require(ts.isFullyReduced)
      require(rts.isFullyReduced)
      new PTypeSubstitution(ts map (kv => rts.rename(kv._1) -> kv._2.substitute(rts)))
    }

    var extraReturnTypeConstraint: Option[PType] = None

    if (poa.typeSubstitutions.isEmpty) {
      poa.args.foreach(t.checkInternal)
      var nestedTypeError = !poa.args.forall(a => a.typ.isValidOrUndeclared)
      poa match {
        case pcc@PConstructorCall(_, _, typeAnnotated) =>
          if (pcc.idnref.decls.isEmpty) {
            nestedTypeError = true
            t.messages ++= FastMessaging.message(pcc.idnref, s"undefined adt constructor `${pcc.idnref.name}`")
          }
          typeAnnotated match {
            case Some((_, ta)) =>
              t.check(ta)
              if (!ta.isValidOrUndeclared) nestedTypeError = true
              if (!nestedTypeError) {
                val adtName = ta.asInstanceOf[PAdtType].adt.name
                if (pcc.idnref.filterDecls(_.adt.idndef.name == adtName)) {
                  nestedTypeError = true
                  t.messages ++= FastMessaging.message(pcc.idnref, s"undefined constructor `${pcc.idnref.name}` in adt `$adtName`")
                } else if (pcc.idnref.decls.length > 1) {
                  nestedTypeError = true
                  t.messages ++= FastMessaging.message(pcc.idnref, s"ambiguous adt constructor `${pcc.idnref.name}` in adt `$adtName`")
                }
              }
            case None =>
              if (pcc.idnref.decls.length > 1) {
                nestedTypeError = true
                t.messages ++= FastMessaging.message(pcc.idnref, s"ambiguous adt constructor `${pcc.idnref.name}`")
              }
          }
          if (!nestedTypeError) {
            val ac = pcc.constructor.get
            t.ensure(ac.formalArgs.size == pcc.args.size, pcc, "wrong number of arguments")
            val adt = ac.adt
            val fdtv = PTypeVar.freshTypeSubstitution((adt.typVarsSeq map (tv => tv.idndef.name)).distinct) //fresh domain type variables
            pcc.adtTypeRenaming = Some(fdtv)
            pcc._extraLocalTypeVariables = (adt.typVarsSeq map (tv => PTypeVar(tv.idndef.name))).toSet
            extraReturnTypeConstraint = pcc.typeAnnotated.map(_._2)
          }

        case pdc@PDestructorCall(rcv, _, name) =>
          rcv.typ match {
            case at: PAdtType =>
              // Otherwise error already reported by `PAdtType.typecheck`
              if (!nestedTypeError && at.adt.decl.isDefined) {
                val adt = at.adt.decl.get.asInstanceOf[PAdt]
                if (name.filterDecls(_.constructor.adt.idndef.name == adt.idndef.name)) {
                  nestedTypeError = true
                  t.messages ++= FastMessaging.message(pdc, s"undefined adt field `${name.name}` when destructing, in adt `${adt.idndef.name}`")
                } else if (name.decl.isEmpty) {
                  nestedTypeError = true
                  t.messages ++= FastMessaging.message(pdc, s"ambiguous adt field `${name.name}` when destructing, in adt `${adt.idndef.name}`")
                } else {
                  val fdtv = PTypeVar.freshTypeSubstitution((adt.typVarsSeq map (tv => tv.idndef.name)).distinct) //fresh domain type variables
                  pdc.adtTypeRenaming = Some(fdtv)
                  pdc._extraLocalTypeVariables = (adt.typVarsSeq map (tv => PTypeVar(tv.idndef.name))).toSet
                }
              }
            case typ =>
              nestedTypeError = true
              t.messages ++= FastMessaging.message(pdc, s"found incompatible receiver type `${typ.pretty}` when destructing adt field `${name.name}`, expected an adt")
          }

        case pdc@PDiscriminatorCall(_, _, is, name) =>
          if (name.decls.isEmpty) {
            nestedTypeError = true
            t.messages ++= FastMessaging.message(pdc, s"undefined adt constructor `${name.name}` when checking `${is.pretty}${name.name}`")
          } else if (name.decl.isEmpty) {
            nestedTypeError = true
            t.messages ++= FastMessaging.message(pdc, s"ambiguous adt constructor `${name.name}` when checking `${is.pretty}${name.name}`")
          } else if (!nestedTypeError) {
            val ac = name.decl.get.asInstanceOf[PAdtConstructor]
            val adt = ac.adt
            val fdtv = PTypeVar.freshTypeSubstitution((adt.typVarsSeq map (tv => tv.idndef.name)).distinct) //fresh domain type variables
            pdc.adtTypeRenaming = Some(fdtv)
            pdc._extraLocalTypeVariables = (adt.typVarsSeq map (tv => PTypeVar(tv.idndef.name))).toSet
          }

        case _ => sys.error("PAdtOpApp#typecheck: unexpectable type")
      }

      if (!nestedTypeError && poa.signatures.nonEmpty && poa.args.forall(_.typeSubstitutions.nonEmpty)) {
        val ltr = getFreshTypeSubstitution(poa.localScope.toList) //local type renaming - fresh versions
        val rlts = poa.signatures map (ts => refreshWith(ts, ltr)) //local substitutions refreshed
        assert(rlts.nonEmpty)
        val rrt: PDomainType = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType] // return type (which is a dummy type variable) replaced with fresh type
        val flat = poa.args.indices map (i => POpApp.pArg(i).substitute(ltr)) //fresh local argument types
        // the tuples below are: (fresh argument type, argument type as used in domain of substitutions, substitutions, the argument itself)
        poa.typeSubstitutions ++= t.unifySequenceWithSubstitutions(rlts, flat.indices.map(i => (poa.args(i).typ, flat(i), poa.args(i).typeSubsDistinct.toSeq, poa.args(i))) ++
          (
            extraReturnTypeConstraint match {
              case None => Nil
              case Some(t) => Seq((t, rrt, List(PTypeSubstitution.id), poa))
            }
            )
        ).getOrElse(Seq())
        val ts = poa.typeSubsDistinct
        if (ts.isEmpty)
          t.typeError(poa)
        poa.typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
      } else {
        poa.typeSubstitutions.clear()
        poa.typ = PUnknown()
      }
    }
    None
  }
}

case class PConstructorCall(idnref: PIdnRef[PAdtConstructor], callArgs: PDelimited.Comma[PSym.Paren, PExp], typeAnnotated: Option[(PSym.Colon, PType)])
                           (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp with PCallLike with PLocationAccess {
  def constructor: Option[PAdtConstructor] = idnref.decl.filter(_.isInstanceOf[PAdtConstructor]).map(_.asInstanceOf[PAdtConstructor])
  def adt: Option[PAdt] = constructor.map(_.adt)
  override def signatures: List[PTypeSubstitution] = {
    if (adt.isDefined && constructor.get.formalArgs.size == args.size) {
      List(
        new PTypeSubstitution(
          args.indices.map(i => POpApp.pArg(i).domain.name -> constructor.get.formalArgs(i).typ.substitute(adtTypeRenaming.get)) :+
            (POpApp.pRes.domain.name -> adt.get.getAdtType.substitute(adtTypeRenaming.get)))
      )
    } else List()
  }

  override def translateExp(t: Translator): Exp = {
    val constructor = PAdtConstructor.findAdtConstructor(idnref, t)
    val actualArgs = args map t.exp
    val so: Option[Map[TypeVar, Type]] = adtSubstitution match {
      case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> t.ttyp(kv._2)))
      case None => None
    }
    so match {
      case Some(s) =>
        val adt = t.getMembers()(constructor.adtName).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtConstructorApp(constructor, actualArgs, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }
}

case class PDestructorCall(rcv: PExp, dot: PReserved[PDiscDot.type], idnref: PIdnRef[PAdtFieldDecl])
                          (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp {
  def field: Option[PAdtFieldDecl] = idnref.decl.filter(_.isInstanceOf[PAdtFieldDecl]).map(_.asInstanceOf[PAdtFieldDecl])
  def adt: Option[PAdt] = field.map(_.constructor.adt)

  override def signatures: List[PTypeSubstitution] = if (adt.isDefined && adtTypeRenaming.isDefined) {
    assert(args.length == 1, s"PDestructorCall: Expected args to be of length 1 but was of length ${args.length}")
    List(
      new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> adt.get.getAdtType.substitute(adtTypeRenaming.get)) :+
          (POpApp.pRes.domain.name -> field.get.typ.substitute(adtTypeRenaming.get)))
    )
  } else List()

  override def args: Seq[PExp] = Seq(rcv)

  override def translateExp(t: Translator): Exp = {
    val actualRcv = t.exp(rcv)
    val so: Option[Map[TypeVar, Type]] = adtSubstitution match {
      case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> t.ttyp(kv._2)))
      case None => None
    }
    so match {
      case Some(s) =>
        val adt = t.getMembers()(this.adt.get.idndef.name).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtDestructorApp(adt, idnref.name, actualRcv, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }
}

case object PIsKeyword extends PKwOp("is") {
  override def rightPad = ""
}
case object PDiscDot extends PSym(".") with PSymbolOp

case class PDiscriminatorCall(rcv: PExp, dot: PReserved[PDiscDot.type], is: PReserved[PIsKeyword.type], idnref: PIdnRef[PAdtConstructor])
                             (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp {
  def constructor: Option[PAdtConstructor] = idnref.decl.filter(_.isInstanceOf[PAdtConstructor]).map(_.asInstanceOf[PAdtConstructor])
  def adt: Option[PAdt] = constructor.map(_.adt)
  override def signatures: List[PTypeSubstitution] = if (adt.isDefined) {
    assert(args.length == 1, s"PDiscriminatorCall: Expected args to be of length 1 but was of length ${args.length}")
    List(
      new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> adt.get.getAdtType.substitute(adtTypeRenaming.get)) :+
          (POpApp.pRes.domain.name -> TypeHelper.Bool))
    )
  } else List()

  override def args: Seq[PExp] = Seq(rcv)

  override def translateExp(t: Translator): Exp = {
    val actualRcv = t.exp(rcv)
    val so: Option[Map[TypeVar, Type]] = adtSubstitution match {
      case Some(ps) => Some(ps.m.map(kv => TypeVar(kv._1) -> t.ttyp(kv._2)))
      case None => None
    }
    so match {
      case Some(s) =>
        val adt = t.getMembers()(this.adt.get.idndef.name).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtDiscriminatorApp(adt, idnref.name, actualRcv, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }
}