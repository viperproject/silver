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
import scala.util.{Success, Try}


case class PAdt(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], constructors: Seq[PAdtConstructor], derivingInfos: Seq[PAdtDerivingInfo])
               (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PExtender with PSingleMember {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ typVars ++ constructors ++ derivingInfos

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    t.checkMember(this) {
      constructors foreach (_.typecheck(t, n))
    }
    // Check that formalArg identifiers among all constructors are unique
    val allFormalArgs = constructors flatMap (_.formalArgs collect { case fad: PFormalArgDecl => fad })
    val duplicateArgs = allFormalArgs.groupBy(_.idndef.name).collect { case (_, ys) if ys.size > 1 => ys.head }.toSeq
    t.messages ++= duplicateArgs.flatMap { arg =>
      FastMessaging.message(arg.idndef, "Duplicate argument identifier `" + arg.idndef.name + "' among adt constructors at " + arg.idndef.pos._1)
    }

    // Check validity blocklisted identifiers
    derivingInfos.foreach { di =>
      val diff = di.blockList.filterNot(allFormalArgs.map(fad => PIdnUse(fad.idndef.name)(fad.idndef.pos)).toSet)
      if (diff.nonEmpty) {
        t.messages ++= FastMessaging.message(diff.head, "Invalid identifier `" + diff.head.name + "' at " + diff.head.pos._1)
      }

    }
    // Check duplicate deriving infos
    val duplicateDerivingInfo = derivingInfos.groupBy(_.idnuse).collect { case (_, ys) if ys.size > 1 => ys.head }.toSeq
    t.messages ++= duplicateDerivingInfo.flatMap { di =>
      FastMessaging.message(di.idnuse, "Duplicate derivation of function `" + di.idnuse.name + "' at " + di.idnuse.pos._1)
    }

    derivingInfos.foreach(_.typecheck(t, n))

    None
  }

  override def translateMemberSignature(t: Translator): Adt = {

    Adt(
      idndef.name,
      null,
      typVars map (t => TypeVar(t.idndef.name)),
      derivingInfos.map(a => (a.idnuse.name, (if (a.param.nonEmpty) Some(t.ttyp(a.param.get)) else None, a.blockList.map(_.name)))).toMap
    )(t.liftPos(this))
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
    val adtType = PAdtType(PIdnUse(idndef.name)(NoPosition, NoPosition), typVars map { t =>
      val typeVar = PDomainType(PIdnUse(t.idndef.name)(NoPosition, NoPosition), Nil)(NoPosition, NoPosition)
      typeVar.kind = PDomainTypeKinds.TypeVar
      typeVar
    })(NoPosition, NoPosition)
    adtType.kind = PAdtTypeKinds.Adt
    adtType
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)] = None, forceRewrite: Boolean = false): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 4, s"PAdt : expected length 4 but got ${children.length}")
      val first = children(0).asInstanceOf[PIdnDef]
      val second = children(1).asInstanceOf[Seq[PTypeVarDecl]]
      val third = children(2).asInstanceOf[Seq[PAdtConstructor]]
      val fourth = children(3).asInstanceOf[Seq[PAdtDerivingInfo]]
      PAdt(first, second, third, fourth)(pos.getOrElse(this.pos), annotations).asInstanceOf[this.type]
    }
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

case class PAdtConstructor(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl])
                          (val adtName: PIdnUse)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PExtender with PSingleMember {

  override val getSubnodes: Seq[PNode] = Seq(idndef) ++ formalArgs

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this.formalArgs foreach (a => t.check(a.typ))

    // Check if there are name clashes for the corresponding discriminator, if so we raise a type-check error
    Try {
      n.definition(t.curMember)(PIdnUse("is" + idndef.name)(idndef.pos))
    } match {
      case Success(Some(decl)) =>
        t.messages ++= FastMessaging.message(idndef, "corresponding adt discriminator identifier `" + decl.idndef.name + "' at " + idndef.pos._1 + " is shadowed at " + decl.idndef.pos._1)
      case _ =>
    }
    None
  }

  override def translateMemberSignature(t: Translator): AdtConstructor = {
    val adt = PAdt.findAdt(adtName, t)
    AdtConstructor(
      adt,
      idndef.name,
      formalArgs map { arg => LocalVarDecl(arg.idndef.name, t.ttyp(arg.typ))(t.liftPos(arg.idndef)) }
    )(t.liftPos(this))
  }

  override def translateMember(t: Translator): AdtConstructor = {
    findAdtConstructor(idndef, t)
  }

  override def withChildren(children: Seq[Any], pos: Option[(Position, Position)] = None, forceRewrite: Boolean = false): this.type = {
    if (!forceRewrite && this.children == children && pos.isEmpty)
      this
    else {
      assert(children.length == 2, s"PAdtConstructor : expected length 2 but got ${children.length}")
      val first = children.head.asInstanceOf[PIdnDef]
      val second = children.tail.head.asInstanceOf[Seq[PFormalArgDecl]]
      PAdtConstructor(first, second)(this.adtName)(pos.getOrElse(this.pos), annotations).asInstanceOf[this.type]
    }
  }
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

case class PAdtConstructor1(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl])(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])])

case class PAdtDerivingInfo(idnuse: PIdnUse, param: Option[PType], blockList: Set[PIdnUse])(val pos: (Position, Position)) extends PExtender {

  override def getSubnodes(): Seq[PNode] = Seq(idnuse) ++ param.toSeq

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    param.foreach(t.check)
    None
  }
}

case class PAdtType(adt: PIdnUse, args: Seq[PType])
                   (val pos: (Position, Position)) extends PExtender with PGenericType {

  var kind: PAdtTypeKinds.Kind = PAdtTypeKinds.Unresolved

  override def genericName: String = adt.name

  override def typeArguments: Seq[PType] = args

  override def isValidOrUndeclared: Boolean = (kind == PAdtTypeKinds.Adt || isUndeclared) && args.forall(_.isValidOrUndeclared)

  override def substitute(ts: PTypeSubstitution): PType = {
    require(kind == PAdtTypeKinds.Adt || isUndeclared)

    val newArgs = args map (a => a.substitute(ts))
    if (args == newArgs)
      return this

    val newAdtType = PAdtType(adt, newArgs)((NoPosition, NoPosition))
    newAdtType.kind = PAdtTypeKinds.Adt
    newAdtType
  }

  def isUndeclared: Boolean = kind == PAdtTypeKinds.Undeclared

  override def getSubnodes(): Seq[PNode] = Seq(adt) ++ args

  override def subNodes: Seq[PType] = args

  override def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = {
    this match {
      case at@PAdtType(_, _) if at.isResolved => None
      /* Already resolved, nothing left to do */
      case at@PAdtType(adt, args) =>
        assert(!at.isResolved, "Only yet-unresolved adt types should be type-checked and resolved")

        args foreach t.check

        var x: Any = null

        try {
          x = t.names.definition(t.curMember)(adt).get
        } catch {
          case _: Throwable =>
        }

        x match {
          case PAdt(_, typVars, _, _) =>
            t.ensure(args.length == typVars.length, this, "wrong number of type arguments")
            at.kind = PAdtTypeKinds.Adt
            None
          case _ =>
            at.kind = PAdtTypeKinds.Undeclared
            Option(Seq(s"found undeclared type ${at.adt.name}"))
        }
    }
  }

  def isResolved: Boolean = kind != PAdtTypeKinds.Unresolved

  override def translateType(t: Translator): Type = {
    t.getMembers().get(adt.name) match {
      case Some(d) =>
        val adt = d.asInstanceOf[Adt]
        val typVarMapping = adt.typVars zip (args map t.ttyp)
        AdtType(adt, typVarMapping.toMap)
      case None => sys.error("undeclared adt type")
    }
  }

  override def withTypeArguments(s: Seq[PType]): PGenericType = copy(args = s)(pos)

  override def toString: String = adt.name + (if (args.isEmpty) "" else s"[${args.mkString(", ")}]")

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
  var adt: PAdt = null
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
      if (!nestedTypeError) {
        poa match {
          case pcc@PConstructorCall(constr, args, typeAnnotated) =>
            typeAnnotated match {
              case Some(ta) =>
                t.check(ta)
                if (!ta.isValidOrUndeclared) nestedTypeError = true
              case None =>
            }

            if (!nestedTypeError) {
              val ac = t.names.definition(t.curMember)(constr).get.asInstanceOf[PAdtConstructor]
              pcc.constructor = ac
              t.ensure(ac.formalArgs.size == args.size, pcc, "wrong number of arguments")
              val adt = t.names.definition(t.curMember)(ac.adtName).get.asInstanceOf[PAdt]
              pcc.adt = adt
              val fdtv = PTypeVar.freshTypeSubstitution((adt.typVars map (tv => tv.idndef.name)).distinct) //fresh domain type variables
              pcc.adtTypeRenaming = Some(fdtv)
              pcc._extraLocalTypeVariables = (adt.typVars map (tv => PTypeVar(tv.idndef.name))).toSet
              extraReturnTypeConstraint = pcc.typeAnnotated
            }

          case pdc@PDestructorCall(name, _) =>
            pdc.args.head.typ match {
              case at: PAdtType =>
                val adt = t.names.definition(t.curMember)(at.adt).get.asInstanceOf[PAdt]
                pdc.adt = adt
                val matchingConstructorArgs: Seq[PFormalArgDecl] = adt.constructors flatMap (c => c.formalArgs.collect { case fad@PFormalArgDecl(idndef, _) if idndef.name == name => fad })
                if (matchingConstructorArgs.nonEmpty) {
                  pdc.matchingConstructorArg = matchingConstructorArgs.head
                  val fdtv = PTypeVar.freshTypeSubstitution((adt.typVars map (tv => tv.idndef.name)).distinct) //fresh domain type variables
                  pdc.adtTypeRenaming = Some(fdtv)
                  pdc._extraLocalTypeVariables = (adt.typVars map (tv => PTypeVar(tv.idndef.name))).toSet
                } else {
                  nestedTypeError = true
                  t.messages ++= FastMessaging.message(pdc, "no matching destructor found")
                }
              case _ =>
                nestedTypeError = true
                t.messages ++= FastMessaging.message(pdc, "expected an adt as receiver")
            }

          case pdc@PDiscriminatorCall(name, _) =>
            t.names.definition(t.curMember)(name) match {
              case Some(ac: PAdtConstructor) =>
                val adt = t.names.definition(t.curMember)(ac.adtName).get.asInstanceOf[PAdt]
                pdc.adt = adt
                val fdtv = PTypeVar.freshTypeSubstitution((adt.typVars map (tv => tv.idndef.name)).distinct) //fresh domain type variables
                pdc.adtTypeRenaming = Some(fdtv)
                pdc._extraLocalTypeVariables = (adt.typVars map (tv => PTypeVar(tv.idndef.name))).toSet
              case _ =>
                nestedTypeError = true
                t.messages ++= FastMessaging.message(pdc, "invalid adt discriminator")
            }

          case _ => sys.error("PAdtOpApp#typecheck: unexpectable type")
        }

        if (poa.signatures.nonEmpty && poa.args.forall(_.typeSubstitutions.nonEmpty) && !nestedTypeError) {
          val ltr = getFreshTypeSubstitution(poa.localScope.toList) //local type renaming - fresh versions
          val rlts = poa.signatures map (ts => refreshWith(ts, ltr)) //local substitutions refreshed
          assert(rlts.nonEmpty)
          val rrt: PDomainType = POpApp.pRes.substitute(ltr).asInstanceOf[PDomainType] // return type (which is a dummy type variable) replaced with fresh type
          val flat = poa.args.indices map (i => POpApp.pArg(i).substitute(ltr)) //fresh local argument types
          // the tuples below are: (fresh argument type, argument type as used in domain of substitutions, substitutions, the argument itself)
          poa.typeSubstitutions ++= t.unifySequenceWithSubstitutions(rlts, flat.indices.map(i => (flat(i), poa.args(i).typ, poa.args(i).typeSubstitutions.distinct.toSeq, poa.args(i))) ++
            (
              extraReturnTypeConstraint match {
                case None => Nil
                case Some(t) => Seq((rrt, t, List(PTypeSubstitution.id), poa))
              }
              )
          ).getOrElse(Seq())
          val ts = poa.typeSubstitutions.distinct
          if (ts.isEmpty)
            t.typeError(poa)
          poa.typ = if (ts.size == 1) rrt.substitute(ts.head) else rrt
        } else {
          poa.typeSubstitutions.clear()
          poa.typ = PUnknown()()
        }
      }
    }
    None
  }
}

case class PConstructorCall(constr: PIdnUse, args: Seq[PExp], typeAnnotated: Option[PType] = None)
                           (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp with PLocationAccess {
  // Following field is set during resolving, respectively in the typecheck method inherited from PAdtOpApp
  var constructor: PAdtConstructor = null

  override def opName: String = constr.name

  override def idnuse: PIdnUse = constr

  override def getSubnodes(): Seq[PNode] = Seq(constr) ++ args ++ (typeAnnotated match {
    case Some(t) => Seq(t)
    case None => Nil
  })

  override def signatures: List[PTypeSubstitution] = {
    if (adt != null && constructor != null && constructor.formalArgs.size == args.size) {
      List(
        new PTypeSubstitution(
          args.indices.map(i => POpApp.pArg(i).domain.name -> constructor.formalArgs(i).typ.substitute(adtTypeRenaming.get)) :+
            (POpApp.pRes.domain.name -> adt.getAdtType.substitute(adtTypeRenaming.get)))
      )
    } else List()
  }

  override def translateExp(t: Translator): Exp = {
    val constructor = PAdtConstructor.findAdtConstructor(constr, t)
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

case class PDestructorCall(name: String, rcv: PExp)
                          (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp {
  // Following field is set during resolving, respectively in the typecheck method inherited from PAdtOpApp
  var matchingConstructorArg: PFormalArgDecl = null

  override def opName: String = name

  override def getSubnodes(): Seq[PNode] = Seq(rcv)

  override def signatures: List[PTypeSubstitution] = if (adt != null && matchingConstructorArg != null) {
    assert(args.length == 1, s"PDestructorCall: Expected args to be of length 1 but was of length ${args.length}")
    List(
      new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> adt.getAdtType.substitute(adtTypeRenaming.get)) :+
          (POpApp.pRes.domain.name -> matchingConstructorArg.typ.substitute(adtTypeRenaming.get)))
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
        val adt = t.getMembers()(this.adt.idndef.name).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtDestructorApp(adt, name, actualRcv, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }
}

case class PDiscriminatorCall(name: PIdnUse, rcv: PExp)
                             (val pos: (Position, Position) = (NoPosition, NoPosition)) extends PAdtOpApp {
  override def opName: String = "is" + name.name

  override def getSubnodes(): Seq[PNode] = Seq(name, rcv)

  override def signatures: List[PTypeSubstitution] = if (adt != null) {
    assert(args.length == 1, s"PDiscriminatorCall: Expected args to be of length 1 but was of length ${args.length}")
    List(
      new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> adt.getAdtType.substitute(adtTypeRenaming.get)) :+
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
        val adt = t.getMembers()(this.adt.idndef.name).asInstanceOf[Adt]
        assert(s.keys.toSet == adt.typVars.toSet)
        AdtDiscriminatorApp(adt, name.name, actualRcv, s)(t.liftPos(this))
      case _ => sys.error("type unification error - should report and not crash")
    }
  }
}