// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder, HasExtraVars, HasExtraValList}
import viper.silver.ast.{Exp, FilePosition, HasLineColumn, Member, NoPosition, Position, SourcePosition, Stmt, Type}
import viper.silver.parser.TypeHelper._
import viper.silver.verifier.ParseReport

import scala.collection.Set
import scala.language.implicitConversions
import java.nio.file.Path

trait Where {
  val pos: (Position, Position)
  def errorPosition: Position = pos match {
        case (slc: FilePosition, flc: HasLineColumn) => SourcePosition(slc.file, slc, flc)
        case (slc: FilePosition, _) => SourcePosition(slc.file, slc.line, slc.column)
        case other => other._1
      }
}

/**
  * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
  * with the actual Viper abstract syntax tree.
  */
trait PNode extends Where with Product with Rewritable with HasExtraValList {

  /* Should output something that can be displayed to the user. */
  def pretty: String

  /** Returns a list of all direct sub-nodes of this node. */
  def subnodes: Seq[PNode] = PNode.children(this, this).flatMap(PNode.nodes(this, _)).toSeq

  /** @see [[Visitor.reduceTree()]] */
  def reduceTree[T](f: (PNode, Seq[T]) => T) = Visitor.reduceTree(this, PNode.callSubnodes)(f)

  /** @see [[Visitor.reduceWithContext()]] */
  def reduceWithContext[C, R](context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R) = {
    Visitor.reduceWithContext(this, PNode.callSubnodes)(context, enter, combine)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f: PartialFunction[PNode, Unit]): Unit = {
    Visitor.visit(this, PNode.callSubnodes)(f)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f1: PartialFunction[PNode, Unit], f2: PartialFunction[PNode, Unit]): Unit = {
    Visitor.visit(this, PNode.callSubnodes, f1, f2)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f: PNode => Boolean): Unit = {
    Visitor.visitOpt(this, PNode.callSubnodes)(f)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f1: PNode => Boolean, f2: PNode => Unit): Unit = {
    Visitor.visitOpt(this, PNode.callSubnodes, f1, f2)
  }

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[A](f: PartialFunction[PNode, A]): Seq[A] =
    Visitor.deepCollect(Seq(this), PNode.callSubnodes)(f)

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[PNode, R]): Seq[R] =
    Visitor.shallowCollect(Seq(this), PNode.callSubnodes)(f)

  /** This method clones the pAST starting from the current node.
    * The pAST is not immutable (certain nodes may have mutable fields).
    * Therefore, additional initialization may be required for the newly created node.
    *
    * The concrete implementations of PNode may introduce [[deepCopy]] methods that would allow
    * creating pAST nodes based on some prototype pAST node, but with changes to some
    * of its fields. For example, [[m.deepCopy( idndef = PIdnDef(s"${m.idndef}_new") )]]
    * will create a pAST node that is identical to [[m]] modulo its [[idndef]] field.
    * Note that the [[deepCopy]] should not be overridng nor overloading deepCopyAll
    * (Its implementation(s) depend on the argument list of a concrete PNode type.)
    *
    * @see [[PNode.initProperties()]] */
  def deepCopyAll[A <: PNode]: PNode =
    StrategyBuilder.Slim[PNode]({ case n => n }).forceCopy().execute[PNode](this)

  private val _children = scala.collection.mutable.ListBuffer[PNode]()

  def getParent: Option[PNode] = parent
  def getAncestor[T](implicit ctag: scala.reflect.ClassTag[T]): Option[T] = {
    var p = getParent
    while (p.isDefined && !ctag.runtimeClass.isInstance(p.get))
      p = p.get.getParent
    p.map(_.asInstanceOf[T])
  }
  def getEnclosingScope: Option[PScope] = getAncestor[PScope]
  def isDescendant[T](implicit ctag: scala.reflect.ClassTag[T]): Boolean = getAncestor[T].isDefined

  private var parent: Option[PNode] = None
  var index: Int = -1
  var next: Option[PNode] = None
  var prev: Option[PNode] = None

  override def initProperties(): Unit = {

    var ind: Int = 0
    var prev: Option[PNode] = None

    _children.clear()
    for (c <- this.subnodes) {
      c.parent = Some(this)
      _children += c
      c.index = ind
      ind += 1
      c.prev = prev
      c.next = None
      prev.foreach(_.next = Some(c))
      prev = Some(c)
      c.initProperties()
    }
  }

  override def getExtraVals: Seq[Any] = Seq(pos)
}

/** Marks that this class contains no PNodes and thus should not be traversed deeper. */
trait PLeaf extends PPrettySubnodes {
  def display: String
}

trait PPrettySubnodes extends PNode {
  override def pretty: String = this match {
    case l: PLeaf => l.display
    case _ => this.prettyMapped()
  }
  def prettyMapped(f: PartialFunction[PNode, String] = PartialFunction.empty): String = this.subnodes map {
    case sn if f.isDefinedAt(sn) => f(sn)
    case l: PLeaf => l.display
    case sn: PPrettySubnodes => sn.prettyMapped(f)
    case sn => sn.pretty
  } mkString ""
}

object PNode {
  def children(parent: PNode, n: Any): Iterator[Any] = {
    n match {
      case _: PLeaf | _: Unit => Iterator.empty
      // Includes `Option`, `Seq`, etc.
      case i: IterableOnce[_] => i.iterator
      // Includes `Either`, all case classes, etc.
      case t: Product => t.productIterator
      // This case should be avoided by marking your node as a `PLeaf`.
      case _ => sys.error(s"Unexpected node type `${n.getClass}`. Make `${parent.getClass}` a `PLeaf` if it has no `PNode` children or put the `${n.getClass}` field into a `PLeaf` wrapper node.")
    }
  }
  def nodes(parent: PNode, n: Any): Iterator[PNode] = {
    n match {
      case n: PNode => Iterator(n)
      case _ => children(parent, n).flatMap(nodes(parent, _))
    }
  }
  def callSubnodes(n: PNode): Seq[PNode] = n.subnodes
}

object TypeHelper {
  val Int = PPrimitiv(PReserved.implied(PKw.Int))(NoPosition, NoPosition)
  val Bool = PPrimitiv(PReserved.implied(PKw.Bool))(NoPosition, NoPosition)
  val Perm = PPrimitiv(PReserved.implied(PKw.Perm))(NoPosition, NoPosition)
  val Ref = PPrimitiv(PReserved.implied(PKw.Ref))(NoPosition, NoPosition)
  val Impure = PBoolImpureType()
  val Wand = PBoolWandType()
  val Predicate = PBoolPredicateType()
  def MakeSet(typ: PType) = PSetType(PReserved.implied(PKw.Set), PGrouped.impliedBracket(typ))(NoPosition, NoPosition)
  def MakeSeq(typ: PType) = PSeqType(PReserved.implied(PKw.Seq), PGrouped.impliedBracket(typ))(NoPosition, NoPosition)
  def MakeMap(key: PType, value: PType) = PMapType(PReserved.implied(PKw.Map), PGrouped.impliedBracket(
      PPairArgument(key, PReserved.implied(PSym.Comma), value)(NoPosition, NoPosition)
    ))(NoPosition, NoPosition)
  def MakeMultiset(typ: PType) = PMultisetType(PReserved.implied(PKw.Multiset), PGrouped.impliedBracket(typ))(NoPosition, NoPosition)

  def commonSupertype(a: PType, b: PType): Option[PType] = {
    (a, b) match {
      case _ if a == b => Some(a)
      case (PFunctionType(args1, res1), PFunctionType(args2, res2)) if args1.length == args2.length =>
        val args = args1.zip(args2).map(p => commonSubtype(p._1, p._2))
        (args.forall(_.isDefined), commonSupertype(res1, res2)) match {
          case (true, Some(res)) => Some(PFunctionType(args.map(_.get), res))
          case _ => None
        }
      case _ => (a.umbrella, b.umbrella) match {
        case (Some(au), Some(bu)) if au == bu => Some(au)
        case (Some(au), None) if au == b => Some(au)
        case (None, Some(bu)) if a == bu => Some(a)
        case _ => None
      }
    }
  }
  def commonSubtype(a: PType, b: PType): Option[PType] = {
    (a, b) match {
      case _ if a == b => Some(a)
      case (PFunctionType(args1, res1), PFunctionType(args2, res2)) if args1.length == args2.length =>
        val args = args1.zip(args2).map(p => commonSupertype(p._1, p._2))
        (args.forall(_.isDefined), commonSubtype(res1, res2)) match {
          case (true, Some(res)) => Some(PFunctionType(args.map(_.get), res))
          case _ => None
        }
      case _ => (a.umbrella, b.umbrella) match {
        case (Some(au), None) if au == b => Some(a)
        case (None, Some(bu)) if a == bu => Some(b)
        case _ => None
      }
    }
  }

  /** Is type `sub` a subtype of type `sup` (i.e. `sub` can be used in a place where `sup` is expected) */
  def isSubtype(sub: PType, sup: PType): Boolean = {
    val commonSup = commonSupertype(sub, sup)
    commonSup.isDefined && commonSup.get == sup
  }
}

///////////////////////////////////////////////////////////////////////////
// Identifiers (uses and definitions)

trait PIdentifier extends PLeaf {
  def name: String
  override def display = name
}

case class PIdnDef(name: String)(val pos: (Position, Position)) extends PNode with PIdentifier

trait PIdnUse extends PNode with PIdentifier {
  def decl: Option[PDeclarationInner]

  // Set for `x` when `x := ...`, set for `f` only when `x.f := ...`
  var assignUse: Boolean = false

  def rename(newName: String): PIdnUse
}
/** Any `PIdnUse` which should have it's `decl` resolved by the `NameAnalyser`. */
sealed trait PIdnUseName[T <: PDeclarationInner] extends PIdnUse {
  implicit def ctag: scala.reflect.ClassTag[T]

  // Could refer to one of these decls
  protected var _decls: Seq[PDeclarationInner] = Nil
  private var _filters: Seq[T => Boolean] = Nil
  def decls: Seq[T] = _decls.flatMap(_ match {
      case d: T => Some(d)
      case _ => None
    }).filter(t => _filters.forall(_(t)))
  override def decl: Option[T] = if (decls.length == 1) Some(decls.head) else None

  def prependDecls(ds: Seq[PDeclarationInner]) = _decls = ds ++ _decls
  def newDecl(d: PDeclarationInner) = _decls :+= d

  /** Filters `decls` according to the given predicate, returns `true` if any are left. */
  def filterDecls(f: T => Boolean): Boolean = {
    _filters :+= f
    decls.isEmpty
  }
}
/** Any `PNode` which should be ignored (as well as it's children) by the `NameAnalyser`. */
trait PNameAnalyserOpaque extends PNode

case class PIdnUseExp(name: String)(val pos: (Position, Position)) extends PIdnUseName[PTypedVarDecl] with PExp with PAssignTarget {
  override def ctag = scala.reflect.classTag[PTypedVarDecl]

  /* Should be set during resolving. Intended to preserve information
   * that is needed by the translator.
   */
  override val typeSubstitutions = List(PTypeSubstitution.id)

  def forceSubstitution(ts: PTypeSubstitution) = {
    typ = typ.substitute(ts)
    assert(typ.isGround)
  }

  override def rename(newName: String) = PIdnUseExp(newName)(pos)
}
case class PIdnRef[T <: PDeclarationInner](name: String)(val pos: (Position, Position))(implicit val ctag: scala.reflect.ClassTag[T]) extends PIdnUseName[T] {
  override def rename(newName: String): PIdnUse = PIdnRef(newName)(pos)
  /** Changes the type of declaration which is referenced, preserves all previously added `decls` but discards `filters`. */
  def retype[U <: PDeclarationInner]()(implicit ctag: scala.reflect.ClassTag[U]): PIdnRef[U] = {
    val newRef = PIdnRef(name)(pos)
    newRef._decls = _decls
    newRef
  }
  def replace(n: PNode): Option[PIdnRef[T]] = n match {
    case n: PIdnUse => Some(PIdnRef(n.name)(n.pos)(ctag))
    case _ => None
  }
  override def getExtraVals: Seq[Any] = Seq(pos, ctag)
}

///////////////////////////////////////////////////////////////////////////
// Variable declarations

trait PAnyFormalArgDecl extends PNode with PUnnamedTypedDeclaration with PPrettySubnodes

/** The declaration of an argument to a domain function. Not a `PDeclaration` as it will never clash. */
case class PDomainFunctionArg(name: Option[PIdnDef], c: Option[PSym.Colon], typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl
object PDomainFunctionArg {
  def apply(d: PIdnTypeBinding): PDomainFunctionArg = PDomainFunctionArg(Some(d.idndef), Some(d.c), d.typ)(d.pos)
}

/** Any `var: Type` style binding, only useful during parsing and therefore not a `PNode`. */
case class PIdnTypeBinding(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position))

/** Anything that can be `PIdnUse`d as an expression (e.g. the receiver of a `PFieldAccess`). */
sealed trait PTypedVarDecl extends PTypedDeclaration with PDeclarationInner with PPrettySubnodes {
  def idndef: PIdnDef
  def toIdnUse: PIdnUseExp = {
    val use = PIdnUseExp(idndef.name)(idndef.pos)
    use.typ = typ
    use.newDecl(this)
    use
  }
}
/** Anything that can be `PIdnUse`d as the target of a `PAssign`. */
sealed trait PAssignableVarDecl extends PTypedVarDecl

/** Any argument to a method, function or predicate. */
case class PFormalArgDecl(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl with PTypedVarDecl with PMemberDeclaration with PMemberUniqueDeclaration
object PFormalArgDecl {
  def apply(d: PIdnTypeBinding): PFormalArgDecl = PFormalArgDecl(d.idndef, d.c, d.typ)(d.pos)
}
/** The return arguments of methods. */
case class PFormalReturnDecl(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position)) extends PAssignableVarDecl with PMemberDeclaration with PMemberUniqueDeclaration
object PFormalReturnDecl {
  def apply(d: PIdnTypeBinding): PFormalReturnDecl = PFormalReturnDecl(d.idndef, d.c, d.typ)(d.pos)
}

case class PLogicalVarDecl(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position)) extends PTypedVarDecl with PLocalDeclaration with PScopeUniqueDeclaration
object PLogicalVarDecl {
  def apply(d: PIdnTypeBinding): PLogicalVarDecl = PLogicalVarDecl(d.idndef, d.c, d.typ)(d.pos)
}
/** Declaration of a local variable. */
case class PLocalVarDecl(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position)) extends PAssignableVarDecl with PLocalDeclaration with PScopeUniqueDeclaration
object PLocalVarDecl {
  def apply(d: PIdnTypeBinding): PLocalVarDecl = PLocalVarDecl(d.idndef, d.c, d.typ)(d.pos)
}
case class PFieldDecl(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position)) extends PTypedDeclaration with PGlobalDeclaration with PGlobalUniqueDeclaration {
  var decl: Option[PFields] = None
  override def annotations = decl.toSeq.flatMap(_.annotations)
  override def pretty = s"${idndef.pretty}: ${typ.pretty}"
}
object PFieldDecl {
  def apply(d: PIdnTypeBinding): PFieldDecl = PFieldDecl(d.idndef, d.c, d.typ)(d.pos)
}

///////////////////////////////////////////////////////////////////////////
// Types

trait PType extends PNode with PPrettySubnodes {
  def isUnknown: Boolean = this.isInstanceOf[PUnknown]
  def isValidOrUndeclared: Boolean
  def isGround: Boolean = true
  def substitute(ts: PTypeSubstitution): PType
  def subNodes: Seq[PType]
  def isPure: Boolean = true
  def umbrella: Option[PType] = None

  //If we add type quantification or any type binders we need to modify this
  def freeTypeVariables: Set[String] =
    subNodes.flatMap(_.freeTypeVariables).toSet union
      (this match {
        case pdt: PDomainType if pdt.isTypeVar && PTypeVar.isFreePTVName(pdt.domain.name) => Set(pdt.genericName)
        case _ => Set()
      })

  override def toString(): String = pretty
}


case class PPrimitiv[T <: PKeywordType](name: PReserved[T])(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType {
  override def isValidOrUndeclared = true
  override def substitute(ts: PTypeSubstitution): PType = this
  override val subNodes = Seq()
  override def umbrella: Option[PType] = name.rs.asInstanceOf[PKeywordType] match {
    case PKw.Bool => Some(TypeHelper.Impure)
    case PKw.Rational => Some(TypeHelper.Perm)
    case _ => None
  }

  override def pretty = name.pretty
}

case class PDomainType(domain: PIdnRef[PTypeDeclaration], args: Option[PDelimited.Comma[PSym.Bracket, PType]])(val pos: (Position, Position)) extends PGenericType with HasExtraVars {
  val genericName = domain.name
  override val typeArguments = typeArgs
  var kind: PDomainTypeKinds.Kind = PDomainTypeKinds.Unresolved
  override val subNodes = typeArgs
  def typeArgs = args.map(_.inner.toSeq).getOrElse(Nil)

  /* This class is also used to represent type variables, as they cannot
   * be distinguished syntactically from domain types without generic arguments.
   * For type variables, we have args.length = 0
   */
  def isTypeVar = kind == PDomainTypeKinds.TypeVar

  override def isValidOrUndeclared =
    (isTypeVar || kind == PDomainTypeKinds.Domain || kind == PDomainTypeKinds.Undeclared) &&
      typeArgs.forall(_.isValidOrUndeclared)

  def isResolved = kind != PDomainTypeKinds.Unresolved

  def isUndeclared = kind == PDomainTypeKinds.Undeclared

  override def isGround: Boolean = {
    typeArgs.forall(_.isGround) && (!isTypeVar || !PTypeVar.isFreePTVName(domain.name))
  }

  override def substitute(ts: PTypeSubstitution): PType = {
    require(kind == PDomainTypeKinds.Domain || kind == PDomainTypeKinds.TypeVar || kind == PDomainTypeKinds.Undeclared)
    if (isTypeVar)
      if (ts.isDefinedAt(domain.name))
        return ts.get(domain.name).get
      else
        return this

    val newArgs = typeArgs map (a => a.substitute(ts))
    if (typeArgs == newArgs)
      return this

    val r = this.withTypeArguments(newArgs)
    r.kind = PDomainTypeKinds.Domain
    r
  }

  override def withTypeArguments(s: Seq[PType]): PDomainType =
    if (s.length == 0 && args.isEmpty) this else copy(args = Some(args.get.update(s)))(pos)

  override def copyExtraVars(from: Any): Unit = this.kind = from.asInstanceOf[PDomainType].kind
}

object PDomainTypeKinds {
  trait Kind
  case object Unresolved extends Kind
  case object Domain extends Kind
  case object TypeVar extends Kind
  case object Undeclared extends Kind
}

object PTypeVar {
  def unapply(pt: PType): Option[String] =
    pt match {
      case pdt: PDomainType if pdt.isTypeVar => Some(pdt.domain.name)
      case _ => None
    }

  def apply(name: String) = {
    val t = PDomainType(PIdnRef(name)((NoPosition, NoPosition)), None)((NoPosition, NoPosition))
    t.kind = PDomainTypeKinds.TypeVar
    t
  }

  val sep = "#"
  val domainNameSep = "%"

  //TODO: do this properly
  def isFreePTVName(s: String) = s.contains(sep)

  private val lastIndex = new AtomicInteger(0)

  //Generate a unique fresh version of old
  def fresh(old: PDomainType) = {
    require(old.isTypeVar)
    val ind = lastIndex.getAndIncrement()
    val freshName = getFreshName(old.domain.name, ind)
    PTypeVar(freshName)
  }

  private def getFreshName(name: String, ind: Int) = name + sep + ind

  def freshTypeSubstitutionPTVs(tvs: Seq[PDomainType]): PTypeRenaming = {
    require(tvs.forall(_.isTypeVar))
    freshTypeSubstitution(tvs map (tv => tv.domain.name))
  }

  def freshTypeSubstitution(tvns: Seq[String], domainName: Option[String] = None): PTypeRenaming = {
    val ind = lastIndex.getAndIncrement()
    new PTypeRenaming((tvns map (tv => {
      val tvName = domainName match {
        case Some(dn) =>
          // Choose a name for the type variable that contains the domain name.
          // This enables us to choose a useful default in case the type variable is unconstrained.
          dn + domainNameSep + tv
        case None => tv
      }
      tv -> getFreshName(tvName, ind)
    })).toMap)
  }
}

trait PGenericType extends PType {
  def genericName: String

  def typeArguments: Seq[PType]

  override def isGround = typeArguments.forall(_.isGround)

  def withTypeArguments(s: Seq[PType]): PGenericType

  override def pretty = {
    val argsPretty = if (typeArguments.isEmpty) "" else typeArguments.map(_.pretty).mkString("[", ", ", "]")
    s"$genericName$argsPretty"
  }
}

sealed trait PGenericCollectionType extends PGenericType {
  def elementType: PGrouped[PSym.Bracket, PType]

  override val typeArguments = Seq(elementType.inner)
  override val subNodes = Seq(elementType.inner)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)

  def update(newType: PType): PGenericCollectionType
  override def substitute(map: PTypeSubstitution) = update(elementType.inner.substitute(map))
  override def withTypeArguments(s: Seq[PType]) = update(s.head)
}

case class PSeqType(seq: PKw.Seq, elementType: PGrouped[PSym.Bracket, PType])(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Seq"
  override def update(newType: PType) = copy(elementType = elementType.update(newType))(pos)
}

case class PSetType(set: PKw.Set, elementType: PGrouped[PSym.Bracket, PType])(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Set"
  override def update(newType: PType) = copy(elementType = elementType.update(newType))(pos)
}

case class PMultisetType(multiset: PKw.Multiset, elementType: PGrouped[PSym.Bracket, PType])(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"
  override def update(newType: PType) = copy(elementType = elementType.update(newType))(pos)
}

case class PMapType(map: PKw.Map, typ: PGrouped[PSym.Bracket, PPairArgument[PType, PType]])(val pos: (Position, Position)) extends PType with PGenericType {
  override val genericName = "Map"
  def keyType = typ.inner.first
  def valueType = typ.inner.second
  override val subNodes = Seq(keyType, valueType)
  override val typeArguments = Seq(keyType, valueType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)

  override def substitute(map: PTypeSubstitution): PMapType =
    copy(typ = typ.update(PPairArgument(keyType.substitute(map), typ.inner.c, valueType.substitute(map))(typ.inner.pos)))(pos)

  override def withTypeArguments(s: Seq[PType]): PMapType =
    copy(typ = typ.update(PPairArgument(s(0), typ.inner.c, s(1))(typ.inner.pos)))(pos)
}

/** Exists temporarily after parsing and is replaced with
 * a real type by macro expansion.
 */
case class PMacroType(use: PCall) extends PType {
  override val pos: (Position, Position) = use.pos
  override def pretty = use.pretty
  override def isValidOrUndeclared: Boolean = ???
  override def substitute(ts: PTypeSubstitution): PType = ???
  override def subNodes: Seq[PType] = ???
}

/** Type used for internal nodes (e.g. typing predicate accesses) - should not be
  * the type of any expression whose value is meaningful in the translation.
  */
sealed trait PInternalType extends PType {
  override val pos: (Position, Position) = (NoPosition, NoPosition)
  override val subNodes: Seq[PType] = Seq()
  override def substitute(ts: PTypeSubstitution) = this
}

// for resolving if something cannot be typed
case class PUnknown() extends PInternalType {
  override def isValidOrUndeclared = false
  override def pretty = "<error>"
}

case class PBoolImpureType() extends PInternalType {
  override def isValidOrUndeclared = true
  override def isPure: Boolean = false
  override def pretty = "<impure>"
}
case class PBoolWandType() extends PInternalType {
  override def isValidOrUndeclared = true
  override def isPure: Boolean = false
  override def umbrella: Option[PType] = Some(TypeHelper.Impure)
  override def pretty = "<wand>"
}
case class PBoolPredicateType() extends PInternalType {
  override def isValidOrUndeclared = true
  override def isPure: Boolean = false
  override def umbrella: Option[PType] = Some(TypeHelper.Impure)
  override def pretty = "<predicate>"
}

/** The type of a `PIdnUse` which refers to a function. Ensures that we get a
 * typecheck error if we try to use a function as a value.
 */
case class PFunctionType(argTypes: Seq[PType], resultType: PType) extends PInternalType {
  override def isValidOrUndeclared: Boolean = subNodes.forall(_.isValidOrUndeclared)
  override def substitute(ts: PTypeSubstitution): PFunctionType =
    PFunctionType(argTypes.map(_.substitute(ts)), resultType.substitute(ts))
  override val subNodes: Seq[PType] = argTypes ++ Seq(resultType)
  override def pretty = {
    val argsPretty = argTypes.map(_.pretty).mkString("(", ", ", ")")
    s"$argsPretty: ${resultType.pretty}"
  }
}

///////////////////////////////////////////////////////////////////////////////////////
// Expressions
// typeSubstitutions are the possible substitutions used for type checking and inference
// The argument types are unified with the (fresh versions of) types  are
trait PExp extends PNode with PPrettySubnodes {
  var brackets: Option[PGrouped.Paren[PExp]] = None
  var typ: PType = PUnknown()

  def typeSubstitutions: scala.collection.Seq[PTypeSubstitution]
  /** Rule out e.g. `Impure && Impure` if `Bool && Bool` is an option (since `Bool <: Impure`). */
  def typeSubsDistinct: scala.collection.Seq[PTypeSubstitution] = {
    val all = typeSubstitutions.distinct.zipWithIndex
    all.filter { case (sub, i) => all.forall {
      case (sup, j) => i == j || !sub.m.forall {
        case (name, t) => sup.m.contains(name) && isSubtype(sup.m(name), t)
      }
    }} map (_._1)
  }

  def forceSubstitution(ts: PTypeSubstitution): Unit

  override def pretty: String = brackets match {
    case Some(b) => s"${b.l.pretty}${super.pretty}${b.r.pretty}"
    case None => super.pretty
  }
}

case class PAnnotatedExp(annotation: PAnnotation, e: PExp)(val pos: (Position, Position)) extends PExp {
  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = e.typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = e.forceSubstitution(ts)
}

trait PSubstitutionMap[S <: PSubstitutionMap[S]] {
  /** Add a new substitution from `a` to `b`. */
  def add[T <: PSubstitutionMap[T]](a: PType, b: PType, default: T): Either[(PType, PType), T]
  /** Insert a substitution which does not yet exist. Should not be called directly. */
  def insert(name: String, t: PType): Either[(PType, PType), S]
  /** Replace a substitution which already exists. Should not be called directly. */
  def replace(name: String, t: PType): S
}

/** An internal map which is temporarily used for construction a substitution for an expression before being `collapse`d. Uses two `PTypeSubstitution` maps,
 * one which is the composition of all maps of subexpressions and the other which is for the signature of the current expression (and `canGeneralise`). */
case class PTypeSubstitutionInternal(m: PTypeSubstitution, added: PTypeSubstitution = PTypeSubstitution(Map(), true)) extends PSubstitutionMap[PTypeSubstitutionInternal] {
  require(!m.canGeneralise && added.canGeneralise)
  def keySet: Set[String] = m.keySet ++ added.keySet
  def get(key: String): Option[PType] = added.get(key).orElse(m.get(key))

  def compose(other: PTypeSubstitution): Either[(PType, PType), PTypeSubstitutionInternal] = {
    val sharedKeys = this.m.keySet.intersect(other.keySet)
    if (sharedKeys.exists(p => this.m.get(p).get != other.get(p).get)) {
      /* no composed substitution if input substitutions do not match */
      val nonMatchingKey = sharedKeys.find(p => this.m.get(p).get != other.get(p).get).get
      return Left((this.m.get(nonMatchingKey).get, other.get(nonMatchingKey).get))
    }

    val newSub = new PTypeSubstitution(
      this.m.map({ case (s: String, pt: PType) => s -> pt.substitute(other) }) ++
        other.map({ case (s: String, pt: PType) => s -> pt.substitute(this.m) }))
    Right(PTypeSubstitutionInternal(newSub, added))
  }

  override def insert(name: String, t: PType): Either[(PType, PType), PTypeSubstitutionInternal] = {
    val newAdded = added.add(name, t)
    if (newAdded.toOption.isDefined)
      Right(PTypeSubstitutionInternal(m, newAdded.toOption.get))
    else
      Left(newAdded.swap.toOption.get)
  }
  override def replace(name: String, t: PType): PTypeSubstitutionInternal = PTypeSubstitutionInternal(m.replace(name, t), added)

  // The expected call sequence is `m.add` -> `this.insert` -> `added.add` -> `added.insert/replace`. We need to call `add` on both
  // sub-maps to ensure that we also `add` any generics with the match case of `PGenericType`.
  override def add[T <: PSubstitutionMap[T]](a: PType, b: PType, default: T = this): Either[(PType, PType), T] =
    m.add(a, b, default)

  def collapse: PTypeSubstitution =
    added.m.foldLeft(m)({
      case (s, (a, b)) => s.substitute(a, b).insert(a, b.substitute(s)).toOption.get
    })
}

/** If `!canGeneralise` this is a substitution map which supports basic add, where we can check if an expression corresponds to some expected type.
 * This is done by calling `add(a, b)` where `a` is the type of the expression and `b` is the expected type of the slot. For example, one might call
 * `add(Int, Bool)` if they see `3 ? ... : ...` and get an error (Left) since `3` is not a subtype of the expected `Bool`.
 * 
 * On the other hand if `canGeneralise` is true, then this is a substitution map which supports generalisation. This means that a call to `add(a, b)`
 * is symmetric in `a` and `b`. For example, one might call `add(Wand, Bool)` if they see `... ? ... --* ... : true` (or more likely will have called
 * `add(#T0, Wand)` and `add(#T0, Bool)` where the second call is turned into `add(Wand, Bool)`) where the type is generalised to `Impure` without error.
 */
case class PTypeSubstitution(m: Map[String, PType], canGeneralise: Boolean = false) extends PSubstitutionMap[PTypeSubstitution]
{
  require(m.values.forall(_.isValidOrUndeclared), s"Invalid type substitution: $m (${m.map(kv => kv._1 -> kv._2.isValidOrUndeclared)})")

  override def insert(name: String, t: PType): Either[(PType, PType), PTypeSubstitution] = {
    require(!m.contains(name))
    Right(substitute(name, t) + (name -> t))
  }
  override def replace(name: String, t: PType): PTypeSubstitution = {
    assert(m.contains(name) && canGeneralise)
    PTypeSubstitution(m + (name -> t), canGeneralise)
  }

  def -(key: String) = new PTypeSubstitution(m.-(key), canGeneralise)

  def get(key: String): Option[PType] = m.get(key)

  private def +(kv: (String, PType)): PTypeSubstitution = new PTypeSubstitution(m + kv, canGeneralise)

  def iterator: Iterator[(String, PType)] = m.iterator

  def isDefinedAt(key: String) = contains(key)

  def keySet: Set[String] = m.keySet

  def restrict(s: Set[String]) = PTypeSubstitution(m.filter(s contains _._1), canGeneralise)

  def map[B](f: ((String, PType)) => B): Seq[B] =
    m.map(f).toSeq

  def contains(key: PDomainType): Boolean = contains(key.domain.name)

  def contains(key: String): Boolean = get(key).nonEmpty

  def substitute(a: String, b: PType): PTypeSubstitution = {
    require(!contains(a), s"Substituting $a -> $b into $this")
    val ts = PTypeSubstitution(Map(a -> b))
    PTypeSubstitution(m.map(kv => kv._1 -> kv._2.substitute(ts)), canGeneralise)
  }

  // The following methods all return a type substitution if successful,
  // otherwise a pair containing the expected and the found type.
  def *(other: PTypeSubstitution): Either[(PType, PType), PTypeSubstitution] =
    other.m.foldLeft(Right(this): Either[(PType, PType), PTypeSubstitution])({
      case (Right(s), p) => s.add(PTypeVar(p._1), p._2)
      case (l@Left(_), _) => l
    })

  def add(a: String, b: PType): Either[(PType, PType), PTypeSubstitution] = add(PTypeVar(a), b)

  /** If `!canGeneralise` then `a` is the type of the expression being used, `b` is the expected type of the slot */
  override def add[T <: PSubstitutionMap[T]](a: PType, b: PType, default: T = this): Either[(PType, PType), T] = {
    val as = a.substitute(this)
    val bs = b.substitute(this)
    if (as == bs) return Right(default)
    val sup = commonSupertype(as, bs)

    // Try to generalise the substitution
    if (canGeneralise) {
      var generalised: Option[T] = None
      a match {
        // The current value in the map (`as`) is less general than the common supertype.
        case PTypeVar(name) if PTypeVar.isFreePTVName(name) && sup.isDefined && sup.get != as =>
          generalised = Some(generalised.getOrElse(default).replace(name, sup.get))
        case _ =>
      }
      b match {
        // The current value in the map (`bs`) is less general than the common supertype.
        case PTypeVar(name) if PTypeVar.isFreePTVName(name) && sup.isDefined && sup.get != bs =>
          generalised = Some(generalised.getOrElse(default).replace(name, sup.get))
        case _ =>
      }
      if (generalised.isDefined)
        return Right(generalised.get)
    }
    // Could not generalise
    (as, bs) match {
      // The slot type is more general than the expression type (all is good)
      case _ if sup.isDefined && sup.get == bs => Right(default)
      // The already present type is the more general one
      case _ if canGeneralise && sup.isDefined && sup.get == as => Right(default)
      case (PTypeVar(name), t) if PTypeVar.isFreePTVName(name) =>
        default.insert(name, t)
      case (t, PTypeVar(name)) if PTypeVar.isFreePTVName(name) =>
        default.insert(name, t)
      case (gt1: PGenericType, gt2: PGenericType) if gt1.genericName == gt2.genericName =>
        val zippedArgs = gt1.typeArguments zip gt2.typeArguments
        (zippedArgs.foldLeft[Either[(PType, PType), T]](Right(default))
          ((ss: Either[(PType, PType), T], p: (PType, PType)) => ss match {
            case Right(sss) => sss.add(p._1, p._2, sss) match {
              case l@Left(pair) =>
                val problemArg = zippedArgs.zipWithIndex.find(_._1 == pair)
                problemArg match {
                  case None => l
                  case Some((_, index)) =>
                    val newArgs = zippedArgs.updated(index, pair)
                    val (argsA, argsB) = newArgs.unzip
                    Left(gt1.withTypeArguments(argsA), gt1.withTypeArguments(argsB))
                }
              case r => r
            }
            case Left((aa, bb)) => Left((aa, bb))
          }))
      case (aa, bb) => Left((aa, bb))
    }

  }

  def this(s: Seq[(String, PType)]) = this(s.toMap)

  def isFullyReduced =
    m.values.forall(pt => (pt.freeTypeVariables intersect m.keySet).isEmpty)

  assert(isFullyReduced)
  //  assert(keySet.forall(PTypeVar.isFreePTVName))
}

object PTypeSubstitution {
  val id = new PTypeSubstitution(Seq())

  implicit def apply(m: Map[String, PType]): PTypeSubstitution = new PTypeSubstitution(m)

  val defaultType = Int
}

class PTypeRenaming(val mm: Map[String, String])
  extends PTypeSubstitution(mm.map(kv => kv._1 -> PTypeVar(kv._2))) {
  def +(kv: (String, String)): PTypeRenaming = new PTypeRenaming(mm + (kv._1 -> kv._2))

  def getS(key: String): Option[String] = mm.get(key)

  def rename(key: String): String = getS(key) match {
    case Some(s) => s
    case None => key
  }
}

///////////////////////////////////////////////////////////////////////////
// Operator applications

trait POpApp extends PExp {
  def args: Seq[PExp]
  /** Which `args` must be pure? Enforced at type checking. */
  def requirePure: Seq[PExp] = Nil

  private val _typeSubstitutions = new scala.collection.mutable.ArrayDeque[PTypeSubstitution]()

  final override def typeSubstitutions = _typeSubstitutions

  def signatures: List[PTypeSubstitution]

  def extraLocalTypeVariables: Set[PDomainType] = Set()

  def localScope: Set[PDomainType] =
    extraLocalTypeVariables union
      Set(POpApp.pRes) union
      args.indices.map(POpApp.pArg).toSet

  def forceSubstitution(ts: PTypeSubstitution) = {
    typeSubstitutions.clear()
    typeSubstitutions += ts
    typ = typ.substitute(ts)
    assert(typ.isGround)
    args.foreach(_.forceSubstitution(ts))
  }
}

object POpApp {
  //type PTypeSubstitution = Map[PDomainType,PType]
  val idPTypeSubstitution = Map[PDomainType, PType]()

  def pArgS(n: Int) = {
    require(n >= 0)
    "#T" + n.toString
  }

  def pResS = "#R"

  def pArg(n: Int) = {
    require(n >= 0)
    PTypeVar(pArgS(n))
  }

  def pRes = PTypeVar(pResS)
}

trait PCallLike extends POpApp {
  override def args = callArgs.inner.toSeq
  def callArgs: PDelimited.Comma[PSym.Paren, PExp]
}

case class PCall(idnref: PIdnRef[PCallable], callArgs: PDelimited.Comma[PSym.Paren, PExp], typeAnnotated: Option[(PSym.Colon, PType)])(val pos: (Position, Position))
  extends PCallLike with PLocationAccess with PAccAssertion with PAssignTarget {
  override def loc = this
  override def perm = PFullPerm.implied()

  override def signatures: List[PTypeSubstitution] = (funcDecl match {
    case Some(pf: PFunction) if pf.formalArgs.size == args.size => List(
        (args.indices.map(i => POpApp.pArgS(i) -> pf.formalArgs(i).typ) :+ (POpApp.pResS -> pf.typ.resultType)).toMap
      )
    case Some(pdf: PDomainFunction) if pdf.formalArgs.size == args.size && domainTypeRenaming.isDefined => List(
        (args.indices.map(i => POpApp.pArgS(i) -> pdf.formalArgs(i).typ.substitute(domainTypeRenaming.get)) :+
            (POpApp.pResS -> pdf.typ.resultType.substitute(domainTypeRenaming.get))).toMap
      )
    case Some(pp: PPredicate) if pp.formalArgs.size == args.size => List(
        (args.indices.map(i => POpApp.pArgS(i) -> pp.formalArgs(i).typ) :+ (POpApp.pResS -> pp.resultType)).toMap
      )
    // this case is handled in Resolver.scala (- method check) which generates the appropriate error message
    case _ => Nil
  })

  def funcDecl: Option[PAnyFunction] = idnref.decl.filter(_.isInstanceOf[PAnyFunction]).map(_.asInstanceOf[PAnyFunction])
  def methodDecl: Option[PMethod] = idnref.decl.filter(_.isInstanceOf[PMethod]).map(_.asInstanceOf[PMethod])
  // def formalArgs: Option[Seq[PFormalArgDecl]] = decl.map(_.formalArgs)

  override def extraLocalTypeVariables = _extraLocalTypeVariables

  var _extraLocalTypeVariables: Set[PDomainType] = Set()
  var domainTypeRenaming: Option[PTypeRenaming] = None

  def isDomainFunction = domainTypeRenaming.isDefined
  def isPredicate = funcDecl.map(_.isInstanceOf[PPredicate]).getOrElse(false)
  def isMethod = methodDecl.isDefined

  var domainSubstitution: Option[PTypeSubstitution] = None

  override def forceSubstitution(ots: PTypeSubstitution) = {

    val ts = domainTypeRenaming match {
      case Some(dtr) =>
        val s3 = PTypeSubstitution(dtr.mm.map(kv => kv._1 -> (ots.get(kv._2) match {
          case Some(pt) => pt
          case None => PTypeSubstitution.defaultType
        })))
        assert(s3.m.keySet == dtr.mm.keySet)
        assert(s3.m.forall(_._2.isGround))
        domainSubstitution = Some(s3)
        dtr.mm.values.foldLeft(ots)(
          (tss, s) => if (tss.contains(s)) tss else tss.add(s, PTypeSubstitution.defaultType).getOrElse(null))
      case _ => ots
    }
    super.forceSubstitution(ts)
    typeSubstitutions.clear()
    typeSubstitutions += ts
    typ = typ.substitute(ts)
    assert(typ.isGround)
    args.foreach(_.forceSubstitution(ts))
  }
}

class PBinExp(val left: PExp, val op: PReserved[PBinaryOp], val right: PExp)(val pos: (Position, Position)) extends POpApp {
  override val args = Seq(left, right)

  override val extraLocalTypeVariables = if (op.rs.isInstanceOf[PCollectionOp]) Set(PCollectionOp.infVar) else Set()
  override def requirePure = if (op.rs.requirePureArgs) args else Nil
  override def signatures: List[PTypeSubstitution] = op.rs.signatures

  override def canEqual(that: Any): Boolean = that.isInstanceOf[PBinExp]

  override def productElement(n: Int): Any = n match {
    case 0 => left
    case 1 => op
    case 2 => right
    case _ => throw new IndexOutOfBoundsException
  }

  override def productArity: Int = 3

  override def equals(that: Any): Boolean = {
    if (this.canEqual(that)) {
      val other = that.asInstanceOf[PBinExp]
      other.op.rs.operator.equals(this.op.rs.operator) && other.right.equals(this.right) && other.left.equals(this.left)
    } else false
  }

  override def hashCode(): Int = viper.silver.utility.Common.generateHashCode(left, op.rs.operator, right)
  override def toString(): String = s"PBinExp($left,$op,$right)"
}

object PBinExp {
  def apply(left: PExp, op: PReserved[PBinaryOp], right: PExp)(pos: (Position, Position)): PBinExp =
    new PBinExp(left, op, right)(pos)

  def unapply(arg: PBinExp): Option[(PExp, PReserved[PBinaryOp], PExp)] = Some(arg.left, arg.op, arg.right)
}

case class PMagicWandExp(override val left: PExp, wand: PSymOp.Wand, override val right: PExp)(override val pos: (Position, Position)) extends PBinExp(left, wand, right)(pos) with PResourceAccess

case class PUnExp(op: PReserved[PUnaryOp], exp: PExp)(val pos: (Position, Position)) extends POpApp {
  override val args = Seq(exp)
  override val signatures = op.rs.signatures
}

case class PCondExp(cond: PExp, q: PSymOp.Question, thn: PExp, c: PSymOp.Colon, els: PExp)(val pos: (Position, Position)) extends POpApp {
  override val args = Seq(cond, thn, els)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(2) -> POpApp.pArg(1), POpApp.pResS -> POpApp.pArg(1))
  )
}

// Simple literals
sealed trait PSimpleLiteral extends PExp {
  override final val typeSubstitutions = Seq(PTypeSubstitution.id)

  def forceSubstitution(ts: PTypeSubstitution) = {}
}

sealed trait PConstantLiteral extends PSimpleLiteral {
  val keyword: PReserved[PKeywordConstant]
}

case class PIntLit(i: BigInt)(val pos: (Position, Position)) extends PSimpleLiteral with PLeaf {
  typ = Int
  override def display = i.toString()
}

case class PResultLit(result: PKw.Result)(val pos: (Position, Position)) extends PSimpleLiteral

case class PBoolLit(keyword: PReserved[PKeywordConstant])(val pos: (Position, Position)) extends PConstantLiteral {
  def b: Boolean = keyword.rs.keyword match {
    case PKw.True.keyword => true
    case PKw.False.keyword => false
  }
  typ = Bool
}

case class PNullLit(keyword: PKw.Null)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Ref
}

sealed trait PHeapOpApp extends POpApp

sealed trait PResourceAccess extends PHeapOpApp

trait PLocationAccess extends PResourceAccess {
  def idnref: PIdnUse
}

case class PFieldAccess(rcv: PExp, dot: PSymOp.Dot, idnref: PIdnRef[PFieldDecl])(val pos: (Position, Position)) extends PLocationAccess with PAssignTarget {
  override final val args = Seq(rcv)

  override def signatures = idnref.decl match {
    case Some(f: PFieldDecl) if f.typ.isValidOrUndeclared && rcv.typ.isValidOrUndeclared => List(
        Map(POpApp.pArgS(0) -> Ref, POpApp.pResS -> f.typ)
      )
    case _ => List()
  }
}

case class PUnfolding(unfolding: PKwOp.Unfolding, acc: PAccAssertion, in: PKwOp.In, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override val args = Seq(acc, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Predicate, POpApp.pResS -> POpApp.pArg(1)))
}

case class PApplying(applying: PKwOp.Applying, wand: PExp, in: PKwOp.In, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override val args = Seq(wand, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Wand, POpApp.pResS -> POpApp.pArg(1)))
}

case class PInhaling(inhaling: PKwOp.Inhaling, exp: PExp, in: PKwOp.In, body: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override val args = Seq(exp, body)
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)),
    Map(POpApp.pArgS(0) -> Impure, POpApp.pResS -> POpApp.pArg(1)),
  )
}

sealed trait PBinder extends PExp with PScope {
  def boundVars: Seq[PLogicalVarDecl]

  def body: PExp

  var _typeSubstitutions: List[PTypeSubstitution] = null

  override def typeSubstitutions = _typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution) = {
    _typeSubstitutions = List(ts)
    typ = typ.substitute(ts)
    body.forceSubstitution(ts)
  }
}

case class PTrigger(exp: PDelimited.Comma[PSym.Brace, PExp])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty = exp.pretty
}

sealed trait PQuantifier extends PBinder {
  def keyword: PReserved[PKeywordLang]
  def c: PSym.ColonColon
  def vars: PDelimited[PLogicalVarDecl, PSym.Comma]
  def triggers: Seq[PTrigger]
  override def boundVars = vars.toSeq
}

case class PExists(keyword: PKw.Exists, vars: PDelimited[PLogicalVarDecl, PSym.Comma], c: PSym.ColonColon, triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForall(keyword: PKw.Forall, vars: PDelimited[PLogicalVarDecl, PSym.Comma], c: PSym.ColonColon, triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForPerm(keyword: PKw.Forperm, vars: PDelimited[PLogicalVarDecl, PSym.Comma], accessRes: PGrouped[PSym.Bracket, PResourceAccess], c: PSym.ColonColon, body: PExp)(val pos: (Position, Position)) extends PQuantifier {
  val triggers: Seq[PTrigger] = Seq()
}

/* Let-expressions `let x == e1 in e2` are represented by the nested structure
 * `PLet(e1, PLetNestedScope(x, e2))`, where `PLetNestedScope <: PScope` (but
 * `PLet` isn't) in order to work with the current architecture of the resolver.
 *
 * More precisely, `NameAnalyser.run` visits a given program to ensure that all
 * used symbol are actually declared. While traversing the program, it
 * pushes/pops `PScope`s to/from the stack. If let-expressions were represented
 * by a flat `PLet(x, e1, e2) <: PScope`, then the let-bound variable `x` would
 * already be in scope while checking `e1`, which wouldn't be correct.
 */
// let variable == exp in nestedScope
case class PLet(l: PKwOp.Let, variable: PIdnDef, eq: PSymOp.EqEq, exp: PGrouped.Paren[PExp], in: PKwOp.In, nestedScope: PLetNestedScope)(val pos: (Position, Position)) extends PExp with PScope {
  def decl: PLogicalVarDecl = PLogicalVarDecl(variable, PReserved.implied(PSym.Colon), exp.inner.typ)(variable.pos)

  override def typeSubstitutions = (for (ts1 <- nestedScope.body.typeSubstitutions; ts2 <- exp.inner.typeSubstitutions) yield (ts1 * ts2).toOption).flatten.toList.distinct
  override def forceSubstitution(ts: PTypeSubstitution) = {
    exp.inner.forceSubstitution(ts)
    nestedScope.body.forceSubstitution(ts)
    typ = nestedScope.body.typ
  }
}

case class PLetNestedScope(body: PExp)(val pos: (Position, Position)) extends PTypedVarDecl with PLocalDeclaration with PScopeUniqueDeclaration {
  def outerLet: PLet = getAncestor[PLet].get
  override def idndef: PIdnDef = outerLet.variable
  override def typ: PType = outerLet.exp.inner.typ
}

// [in,ex]
case class PInhaleExhaleExp(l: PSymOp.LBracket, in: PExp, c: PSymOp.Comma, ex: PExp, r: PSymOp.RBracket)(val pos: (Position, Position)) extends PHeapOpApp {
  override val args = Seq(in, ex)

  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool),
    Map(POpApp.pArgS(0) -> Impure, POpApp.pArgS(1) -> Impure, POpApp.pResS -> Impure),
  )
}

case class PNoPerm(keyword: PKw.None)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PFullPerm(keyword: PKw.Write)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}
object PFullPerm {
  def implied(): PFullPerm = PFullPerm(PReserved(PKw.Write)(NoPosition, NoPosition))(NoPosition, NoPosition)
}

case class PWildcard(keyword: PKw.Wildcard)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PEpsilon(keyword: PKw.Epsilon)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

trait PCallKeyword extends POpApp {
  def op: PReserved[POperatorKeyword]
}

case class PCurPerm(op: PKwOp.Perm, res: PGrouped.Paren[PResourceAccess])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(res.inner)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> Perm)
  )
}

case class PPairArgument[+T, +U](first: T, c: PSym.Comma, second: U)(val pos: (Position, Position)) extends PNode with PPrettySubnodes
case class PMaybePairArgument[+T, +U](first: T, second: Option[(PSym.Comma, U)])(val pos: (Position, Position)) extends PNode with PPrettySubnodes

sealed trait PAccAssertion extends PExp {
  def loc: PLocationAccess
  def perm: PExp
}

case class PAccPred(op: PKwOp.Acc, amount: PGrouped.Paren[PMaybePairArgument[PLocationAccess, PExp]])(val pos: (Position, Position)) extends PCallKeyword with PAccAssertion {
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Predicate, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Predicate),
    Map(POpApp.pArgS(1) -> Perm, POpApp.pResS -> Impure),
  )
  def loc = amount.inner.first
  def perm = amount.inner.second.map(_._2).getOrElse(PFullPerm.implied())
  override val args = Seq(loc, perm)
}

case class POldExp(op: PKwOp.Old, label: Option[PGrouped[PSym.Bracket, Either[PKw.Lhs, PIdnRef[PLabel]]]], e: PGrouped.Paren[PExp])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(e.inner)
  override def requirePure = args
  override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))
}

sealed trait PCollectionLiteral extends PCallKeyword {
  override def args: Seq[PExp] = callArgs.inner.toSeq
  def callArgs: PDelimited.Comma[PSym.Paren, PExp]
  def pElementType: PType

  def pCollectionType(pType: PType): PType

  def explicitType: Option[PType]
}

sealed trait PEmptyCollectionLiteral extends PCollectionLiteral {
  override def pElementType = pAnnotatedType.map(_.inner).getOrElse(PTypeVar("#E"))
  def pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]]

  override val extraLocalTypeVariables: Set[PDomainType] =
    pElementType match {
      case pdt: PDomainType if pdt.isTypeVar => Set(pdt)
      case _ => Set()
    }

  override def signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pResS -> pCollectionType(pElementType)))

  override def explicitType: Option[PType] = pElementType match {
      case PTypeVar("#E") => None
      case tp => Some(tp)
    }
}

sealed trait PExplicitCollectionLiteral extends PCollectionLiteral {
  override val signatures: List[PTypeSubstitution] =
    List(
      ((0 until args.size) map
        (n => if (n == 0) POpApp.pResS -> pCollectionType(POpApp.pArg(0)) else POpApp.pArgS(n) -> POpApp.pArg(0))).toMap
    )

  override val pElementType = args.head.typ
  override def explicitType: Option[PType] = None
}

sealed trait PSeqLiteral extends PCollectionLiteral {
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown() else MakeSeq(pType)
}

case class PEmptySeq(op: PKwOp.Seq, pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PSeqLiteral with PEmptyCollectionLiteral

case class PExplicitSeq(op: PKwOp.Seq, callArgs: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PSeqLiteral with PExplicitCollectionLiteral

// [low..high)
case class PRangeSeq(l: PSymOp.LBracket, low: PExp, ds: PSymOp.DotDot, high: PExp, r: PSymOp.RParen)(val pos: (Position, Position)) extends POpApp {
  override val args = Seq(low, high)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(Int)))
}

// base[idx]
case class PLookup(base: PExp, l: PSymOp.LBracket, idx: PExp, r: PSymOp.RBracket)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)

  override val args = Seq(base, idx)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(POpApp.pRes), POpApp.pArgS(1) -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, POpApp.pRes))
  )
}

case class PSeqSlice(seq: PExp, l: PSymOp.LBracket, s: Option[PExp], d: PSymOp.DotDot, e: Option[PExp], r: PSymOp.RBracket)(val pos: (Position, Position)) extends POpApp {
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = seq +: (s.toSeq ++ e.toSeq)
  override val signatures: List[PTypeSubstitution] = List(Map(
        POpApp.pArgS(0) -> MakeSeq(elementType),
        POpApp.pResS -> MakeSeq(elementType)
    ) ++ ((s, e) match {
    case (Some(_), Some(_)) => Map(POpApp.pArgS(1) -> Int, POpApp.pArgS(2) -> Int)
    case (Some(_), None) | (None, Some(_)) => Map(POpApp.pArgS(1) -> Int)
    case (None, None) => Map() 
  }))
}

case class PUpdate(base: PExp, l: PSymOp.LBracket, key: PExp, a: PSymOp.Assign, value: PExp, r: PSymOp.RBracket)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)
  val elementType: PDomainType = POpApp.pArg(2)

  override val args = Seq(base, key, value)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, elementType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(elementType), POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(elementType)),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, elementType), POpApp.pResS -> MakeMap(keyType, elementType))
  )
}

case class PSize(l: PSymOp.Or, seq: PExp, r: PSymOp.Or)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val elementType: PDomainType = PTypeVar("#E")

  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, elementType)
  override val args = Seq(seq)

  override val signatures: List[PTypeSubstitution] = List(
    // Maps:
    Map(POpApp.pArgS(0) -> MakeSeq(elementType), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> MakeSet(elementType), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> MakeMultiset(elementType), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, elementType), POpApp.pResS -> Int)
  )
}

sealed trait PSetLiteral extends PCollectionLiteral {
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown() else MakeSet(pType)
}

case class PEmptySet(op: PKwOp.Set, pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PSetLiteral with PEmptyCollectionLiteral

case class PExplicitSet(op: PKwOp.Set, callArgs: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral {
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown() else MakeMultiset(pType)
}

case class PEmptyMultiset(op: PKwOp.Multiset, pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PMultiSetLiteral with PEmptyCollectionLiteral

case class PExplicitMultiset(op: PKwOp.Multiset, callArgs: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PMultiSetLiteral with PExplicitCollectionLiteral


/* ** Maps */

sealed trait PMapLiteral extends POpApp {
  override def args: Seq[PExp] = callArgs.inner.toSeq
  def callArgs: PDelimited.Comma[PSym.Paren, PExp]
  def pKeyType: PType
  def pValueType: PType

  def pMapType(keyType: PType, valueType: PType): PType =
    if (keyType.isUnknown || valueType.isUnknown) PUnknown()
    else MakeMap(keyType, valueType)
}

case class PEmptyMap(op: PKwOp.Map, pAnnotatedType: Option[PGrouped[PSym.Bracket, PPairArgument[PType, PType]]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PMapLiteral {
  override val args = Seq()
  override def pKeyType = pAnnotatedType.map(_.inner.first).getOrElse(PTypeVar("#K"))
  override def pValueType = pAnnotatedType.map(_.inner.second).getOrElse(PTypeVar("#E"))

  override val extraLocalTypeVariables: Set[PDomainType] =
    Set(pKeyType, pValueType) collect { case t: PDomainType if t.isTypeVar => t }

  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> pMapType(pKeyType, pValueType)
  ))

  def explicitType: Option[(PType, PType)] = pAnnotatedType.map(t => (t.inner.first, t.inner.second))
}

case class PExplicitMap(op: PKwOp.Map, callArgs: PDelimited.Comma[PSym.Paren, PMaplet])(val pos: (Position, Position)) extends PMapLiteral {
  override def pKeyType: PType = callArgs.inner.head.key.typ
  override def pValueType: PType = callArgs.inner.head.value.typ

  override def signatures: List[PTypeSubstitution] = List(
    (0 until callArgs.inner.length).map {
      case 0 => POpApp.pResS -> POpApp.pArg(0)
      case n => POpApp.pArgS(n) -> POpApp.pArg(0)
    }.toMap
  )
}

/**
  * A key-value pair (i.e., an entry of an `PExplicitMap`) is
  * considered to be a singleton map literal itself.
  */
case class PMaplet(key: PExp, a: PSymOp.Assign, value: PExp)(val pos: (Position, Position)) extends POpApp with PPrettySubnodes {
  override def args: Seq[PExp] = Seq(key, value)
  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> MakeMap(POpApp.pArg(0), POpApp.pArg(1))
  ))
}

case class PMapDomain(keyword: PKwOp.Domain, base: PGrouped.Paren[PExp])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val args = Seq(base.inner)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(keyType)
  ))
}

case class PMapRange(keyword: PKwOp.Range, base: PGrouped.Paren[PExp])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val args = Seq(base.inner)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(valueType)
  ))
}


///////////////////////////////////////////////////////////////////////////
// Statements
trait PStmt extends PNode with PPrettySubnodes

case class PAnnotatedStmt(annotation: PAnnotation, stmt: PStmt)(val pos: (Position, Position)) extends PStmt

case class PSeqn(ss: PDelimited.Block[PStmt])(val pos: (Position, Position)) extends PStmt with PScope {
  override def pretty = ss.prettyLines
}

/**
  * PSeqn representing the expanded body of a statement macro.
  * Unlike a normal PSeqn, it does not represent its own scope.
  * Is created only temporarily during macro expansion and eliminated (i.e., expanded into the surrounding scope)
  * before translation.
  */
case class PMacroSeqn(ss: PDelimited.Block[PStmt])(val pos: (Position, Position)) extends PStmt

case class PFold(fold: PKw.Fold, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PUnfold(unfold: PKw.Unfold, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PPackageWand(pckg: PKw.Package, e: PExp, proofScript: Option[PSeqn])(val pos: (Position, Position)) extends PStmt

case class PApplyWand(apply: PKw.Apply, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PExhale(exhale: PKw.Exhale, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssert(assert: PKw.Assert, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssume(assume: PKw.Assume, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PInhale(inhale: PKw.Inhale, e: PExp)(val pos: (Position, Position)) extends PStmt

/** Can also represent a method call or statement macro with no `:=` when `targets` is empty. */
case class PAssign(targets: PDelimited[PExp with PAssignTarget, PSym.Comma], op: Option[PSymOp.Assign], rhs: PExp)(val pos: (Position, Position)) extends PStmt

sealed trait PIfContinuation extends PStmt
case class PIf(keyword: PReserved[PKeywordIf], cond: PGrouped.Paren[PExp], thn: PSeqn, els: Option[PIfContinuation])(val pos: (Position, Position)) extends PStmt with PIfContinuation
case class PElse(k: PKw.Else, els: PSeqn)(val pos: (Position, Position)) extends PStmt with PIfContinuation

case class PWhile(keyword: PKw.While, cond: PGrouped.Paren[PExp], invs: PDelimited[PSpecification[PKw.InvSpec], Option[PSym.Semi]], body: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PVars(keyword: PKw.Var, vars: PDelimited[PLocalVarDecl, PSym.Comma], init: Option[(PSymOp.Assign, PExp)])(val pos: (Position, Position)) extends PStmt {
  def assign: Option[PAssign] = init map (i => PAssign(vars.update(vars.toSeq.map(_.toIdnUse)), Some(i._1), i._2)(pos))
}

case class PLabel(label: PKw.Label, idndef: PIdnDef, invs: PDelimited[PSpecification[PKw.InvSpec], Option[PSym.Semi]])(val pos: (Position, Position)) extends PStmt with PMemberDeclaration with PBackwardDeclaration

case class PGoto(goto: PKw.Goto, target: PIdnRef[PLabel])(val pos: (Position, Position)) extends PStmt

// Should this be sealed?
sealed trait PTypeDeclaration extends PDeclarationInner

case class PTypeVarDecl(idndef: PIdnDef)(val pos: (Position, Position)) extends PMemberDeclaration with PTypeDeclaration with PPrettySubnodes

case class PSkip()(val pos: (Position, Position)) extends PStmt

case class PQuasihavoc(quasihavoc: PKw.Quasihavoc, lhs: Option[(PExp, PSymOp.Implies)], e: PExp)(val pos: (Position, Position)) extends PStmt

case class PQuasihavocall(quasihavocall: PKw.Quasihavocall, vars: PDelimited[PLogicalVarDecl, PSym.Comma], colons: PSym.ColonColon, lhs: Option[(PExp, PSymOp.Implies)], e: PExp)(val pos: (Position, Position)) extends PStmt with PScope

/* new(f1, ..., fn) or new(*) */
case class PNewExp(keyword: PKw.New, fields: PGrouped.Paren[Either[PSym.Star, PDelimited[PIdnRef[PFieldDecl], PSym.Comma]]])(val pos: (Position, Position)) extends PExp {
  override final val typeSubstitutions = Seq(PTypeSubstitution.id)
  def forceSubstitution(ts: PTypeSubstitution) = {}
}

sealed trait PScope extends PNode {
  val scopeId = PScope.uniqueId()
}

object PScope {
  type Id = Long

  private[this] val counter = new AtomicLong(0)

  private def uniqueId() = {
    val id = counter.getAndIncrement()

    id
  }
}

// Annotations
trait PAnnotated extends PNode {
  def annotations: Seq[PAnnotation]
}

// Assignments
sealed trait PAssignTarget

// Declarations

/** An entity is a declaration (named) or an error node */
sealed trait PEntity

trait PDeclarationInner extends PNode {
  def idndef: PIdnDef
}

sealed trait PDeclaration extends PDeclarationInner with PEntity

sealed trait PUniqueDeclaration

// Unique within contained `PProgram`, can only be attached to `PGlobalDeclaration`
trait PGlobalUniqueDeclaration extends PUniqueDeclaration

// Unique within contained `PMember`
trait PMemberUniqueDeclaration extends PUniqueDeclaration

// Unique within contained `PScope` (but not necessarily parent or child scopes)
trait PScopeUniqueDeclaration extends PUniqueDeclaration

// Can be referenced before declaration
trait PBackwardDeclaration

// A declaration which shadows any previous declarations with the same name
trait POverridesDeclaration

sealed trait PUnnamedTypedDeclaration extends PNode {
  def typ: PType
}

// Can be referenced from anywhere within the `PProgram` (needs `PBackwardDeclaration` since PProgram reorders declarations)
trait PGlobalDeclaration extends PDeclaration with PBackwardDeclaration with PAnnotated

// Can be referenced from anywhere within the containing `PMember`
trait PMemberDeclaration extends PDeclaration

// Can be referenced from anywhere within the containing `PScope`
trait PLocalDeclaration extends PDeclaration

trait PTypedDeclaration extends PUnnamedTypedDeclaration

case class PBracedExp(e: PGrouped[PSym.Brace, PExp])(val pos: (Position, Position)) extends PNode {
  override def pretty = s" ${e.l.pretty}\n  ${e.inner.pretty.replace("\n", "\n  ")}\n${e.r.pretty}"
}

trait PCallable extends PDeclarationInner {
  def keyword: PReserved[PKeywordLang]
  def idndef: PIdnDef
  def args: PDelimited.Comma[PSym.Paren, PAnyFormalArgDecl]
  def returnNodes: Seq[PNode]
  def pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]]
  def posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]]
  def body: Option[PNode]

  def formalArgs: Seq[PAnyFormalArgDecl] = args.inner.toSeq
}

trait PGlobalCallable extends PCallable with PGlobalDeclaration
trait PGlobalCallableNamedArgs extends PGlobalCallable {
  override def args: PDelimited.Comma[PSym.Paren, PFormalArgDecl]
  override def formalArgs: Seq[PFormalArgDecl] = args.inner.toSeq
}

abstract class PErrorEntity extends PEntity {
  def name: String
}

// a member (like method or axiom) that is its own name scope
trait PMember extends PScope with PAnnotated {
  def declares: Seq[PGlobalDeclaration]
}

/** Anything that is a PMember and declares only a single thing (itself) */
trait PSingleMember extends PMember with PGlobalDeclaration with PGlobalUniqueDeclaration {
  override def declares = Seq(this)
}

trait PAnyFunction extends PScope with PTypedDeclaration with PGlobalCallable {
  def c: PSym.Colon
  def resultType: PType
  override def typ: PFunctionType = PFunctionType(formalArgs.map(_.typ), resultType)

  override def returnNodes: Seq[PNode] = Seq(c, resultType)
}

trait PNoSpecsFunction extends PAnyFunction {
  override def pres = PDelimited.empty
  override def posts = PDelimited.empty
}

///////////////////////////////////////////////////////////////////////////
// Program Members

case class PProgram(imported: Seq[PProgram], members: Seq[PMember])(val pos: (Position, Position), val localErrors: Seq[ParseReport]) extends PNode {
  val imports: Seq[PImport] = members.collect { case i: PImport => i } ++ imported.flatMap(_.imports)
  val macros: Seq[PDefine] = members.collect { case m: PDefine => m } ++ imported.flatMap(_.macros)
  val domains: Seq[PDomain] = members.collect { case d: PDomain => d } ++ imported.flatMap(_.domains)
  val fields: Seq[PFields] = members.collect { case f: PFields => f } ++ imported.flatMap(_.fields)
  val functions: Seq[PFunction] = members.collect { case f: PFunction => f } ++ imported.flatMap(_.functions)
  val predicates: Seq[PPredicate] = members.collect { case p: PPredicate => p } ++ imported.flatMap(_.predicates)
  val methods: Seq[PMethod] = members.collect { case m: PMethod => m } ++ imported.flatMap(_.methods)
  val extensions: Seq[PExtender] = members.collect { case e: PExtender => e } ++ imported.flatMap(_.extensions)
  val errors: Seq[ParseReport] = localErrors ++ imported.flatMap(_.errors)

  override def pretty = {
    val prefix = if (pos._1.isInstanceOf[FilePosition]) s"// ${pos._1.asInstanceOf[FilePosition].file.toString()} \n" else ""
    val m = members.map(_.pretty).mkString("\n")
    val i = imported.map(_.pretty).mkString("\n")
    prefix + m + "\n\n" + i
  }
  // Pretty print members in a specific order
  def prettyOrdered: String = {
    val all = Seq(imports, macros, domains, fields, functions, predicates, methods, extensions).filter(_.length > 0)
    all.map(_.map(_.pretty).mkString("\n")).mkString("\n")
  }

  override def getExtraVals: Seq[Any] = Seq(pos, localErrors)

  def filterMembers(f: PMember => Boolean): PProgram = PProgram(imported.map(_.filterMembers(f)), members.filter(f))(pos, localErrors)
  def newImported(newImported: Seq[PProgram]): PProgram = if (newImported.isEmpty) this else PProgram(imported ++ newImported, members)(pos, localErrors)
}

object PProgram {
  def error(error: ParseReport): PProgram = PProgram(Nil, Nil)((error.pos, error.pos), Seq(error))
}

case class PImport(annotations: Seq[PAnnotation], imprt: PKw.Import, file: PStringLiteral)(val pos: (FilePosition, FilePosition)) extends PMember with PPrettySubnodes {
  var local: Boolean = true
  var resolved: Option[Path] = None
  def declares = Nil
}

case class PDefineParam(idndef: PIdnDef)(val pos: (Position, Position)) extends PNode with PLocalDeclaration with PPrettySubnodes

case class PDefine(annotations: Seq[PAnnotation], define: PKw.Define, idndef: PIdnDef, parameters: Option[PDelimited.Comma[PSym.Paren, PDefineParam]], body: PNode)(val pos: (FilePosition, FilePosition)) extends PSingleMember with PStmt with PNameAnalyserOpaque

case class PDomain(annotations: Seq[PAnnotation], domain: PKw.Domain, idndef: PIdnDef, typVars: Option[PDelimited.Comma[PSym.Bracket, PTypeVarDecl]], interpretations: Option[PDomainInterpretations], members: PGrouped[PSym.Brace, PDomainMembers])
                  (val pos: (Position, Position)) extends PSingleMember with PTypeDeclaration with PPrettySubnodes {
  def typVarsSeq: Seq[PTypeVarDecl] = typVars.map(_.inner.toSeq).getOrElse(Nil)
}

case class PDomainFunctionInterpretation(k: PKw.Interpretation, i: PStringLiteral)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty = s"\n  ${super.pretty}"
}
trait PDomainMember extends PScope {
  def domain: PDomain = getAncestor[PDomain].get
}
case class PDomainFunction(annotations: Seq[PAnnotation], unique: Option[PKw.Unique], keyword: PKw.FunctionD, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PDomainFunctionArg], c: PSym.Colon, resultType: PType, interpretation: Option[PDomainFunctionInterpretation])(val pos: (Position, Position)) extends PSingleMember with PNoSpecsFunction with PDomainMember with PPrettySubnodes {
  override def body = None
}

case class PAxiom(annotations: Seq[PAnnotation], axiom: PKw.Axiom, idndef: Option[PIdnDef], exp: PBracedExp)(val pos: (Position, Position)) extends PDomainMember with PPrettySubnodes
case class PDomainMembers(funcs: PDelimited[PDomainFunction, Option[PSym.Semi]], axioms: PDelimited[PAxiom, Option[PSym.Semi]])(val pos: (Position, Position)) extends PNode {
  override def pretty: String = {
    val fPretty = if (funcs.length == 0) "" else s"\n  ${funcs.prettyLines.replace("\n", "\n  ")}\n"
    val aPretty = if (axioms.length == 0) "" else s"\n  ${axioms.prettyLines.replace("\n", "\n  ")}\n"
    s"${fPretty}${aPretty}"
  }
}

case class PDomainInterpretation(name: PRawString, c: PSym.Colon, lit: PStringLiteral)(val pos: (Position, Position)) extends PNode with PPrettySubnodes
case class PDomainInterpretations(k: PReserved[PKeywordLang], m: PDelimited.Comma[PSym.Paren, PDomainInterpretation])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def interps: Map[String, String] = m.inner.toSeq.map(i => i.name.str -> i.lit.str).toMap
}

trait PDomainMember1 extends PNode with PPrettySubnodes
case class PDomainFunction1(annotations: Seq[PAnnotation], unique: Option[PKw.Unique], function: PKw.FunctionD, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PDomainFunctionArg], c: PSym.Colon, typ: PType, interpretation: Option[PDomainFunctionInterpretation], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PDomainMember1
case class PAxiom1(annotations: Seq[PAnnotation], axiom: PKw.Axiom, idndef: Option[PIdnDef], exp: PBracedExp, s: Option[PSym.Semi])(val pos: (Position, Position)) extends PDomainMember1
case class PDomainMembers1(members: Seq[PDomainMember1])(val pos: (Position, Position)) extends PNode with PPrettySubnodes


case class PFields(annotations: Seq[PAnnotation], field: PKw.Field, fields: PDelimited[PFieldDecl, PSym.Comma], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PMember with PPrettySubnodes {
  override def declares: Seq[PGlobalDeclaration] = fields.toSeq
}

case class PSpecification[+T <: PKw.Spec](k: PReserved[PKw.Spec], e: PExp)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty: String = "\n  " + super.pretty
}

case class PFunction(annotations: Seq[PAnnotation], keyword: PKw.Function, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], c: PSym.Colon, resultType: PType, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]], posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]], body: Option[PBracedExp])
                    (val pos: (Position, Position)) extends PSingleMember with PAnyFunction with PGlobalCallableNamedArgs with PPrettySubnodes

case class PPredicate(annotations: Seq[PAnnotation], keyword: PKw.Predicate, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], body: Option[PBracedExp])(val pos: (Position, Position))
  extends PSingleMember with PNoSpecsFunction with PGlobalCallableNamedArgs with PPrettySubnodes {
  override def c = PReserved.implied(PSym.Colon)
  override def resultType = Predicate
}

case class PMethod(annotations: Seq[PAnnotation], keyword: PKw.Method, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], returns: Option[PMethodReturns], pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]], posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]], body: Option[PSeqn])
                  (val pos: (Position, Position)) extends PSingleMember with PGlobalCallableNamedArgs with PPrettySubnodes {
  def formalReturns: Seq[PFormalReturnDecl] = returns.map(_.formalReturns.inner.toSeq).getOrElse(Nil)
  override def returnNodes = returns.toSeq
}

case class PMethodReturns(k: PKw.Returns, formalReturns: PGrouped.Paren[PDelimited[PFormalReturnDecl, PSym.Comma]])(val pos: (Position, Position)) extends PNode with PPrettySubnodes

/**
  * Used for parsing annotation for top level members. Passed as an argument to the members to construct them.
  */
case class PAnnotationsPosition(annotations: Seq[PAnnotation], pos: (FilePosition, FilePosition))

case class PAnnotation(at: PSym.At, key: PRawString, values: PGrouped.Paren[PDelimited[PStringLiteral, PSym.Comma]])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty: String = super.pretty + "\n"
}

// Any unenclosed string (e.g. `hello`)
case class PRawString(str: String)(val pos: (Position, Position)) extends PNode with PLeaf {
  override def display: String = str
}

// Any enclosed string (e.g. `"hello"`)
case class PStringLiteral(grouped: PGrouped[_, PRawString])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def str: String = grouped.inner.str
}

trait PExtender extends PNode {
  def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = ???

  def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = ???

  def translateMemberSignature(t: Translator): Member = ???

  def translateMember(t: Translator): Member = ???

  def translateStmt(t: Translator): Stmt = ???

  def translateExp(t: Translator): Exp = ???

  def translateType(t: Translator): Type = ???
}
