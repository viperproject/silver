// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder}
import viper.silver.ast.{Exp, Member, NoPosition, Position, Stmt, Type}
import viper.silver.parser.TypeHelper._
import viper.silver.verifier.ParseReport

import scala.collection.Set
import scala.language.implicitConversions
import java.nio.file.Path

// TODO: remove
import viper.silver.ast.utility.lsp._

trait Where {
  val pos: (Position, Position)
}

/**
  * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
  * with the actual Viper abstract syntax tree.
  */
trait PNode extends Where with Product with Rewritable {

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

  // /** @see [[Transformer.transform()]] */
  // def transform(pre: PartialFunction[PNode, PNode] = PartialFunction.empty)
  //              (recursive: PNode => Boolean = !pre.isDefinedAt(_),
  //               post: PartialFunction[PNode, PNode] = PartialFunction.empty,
  //               allowChangingNodeType: Boolean = false,
  //               resultCheck: PartialFunction[(PNode, PNode), Unit] = PartialFunction.empty)
  // : this.type =
  //   Transformer.transform[this.type](this, pre)(recursive, post, allowChangingNodeType, resultCheck)

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


  var parent: Option[PNode] = None
  var index: Int = -1
  var next: Option[PNode] = None
  var prev: Option[PNode] = None

  def initProperties(): Unit = {

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

  def getEnclosingScope: Option[PScope] = {
    var p = parent
    while (p.isDefined && !p.get.isInstanceOf[PScope])
      p = p.get.parent
    p.map(_.asInstanceOf[PScope])
  }
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
  val Wand = PWandType()(NoPosition, NoPosition)
  def MakeSet(typ: PType) = PSetType(PReserved.implied(PKw.Set), PGrouped.impliedBracket(typ))(NoPosition, NoPosition)
  def MakeSeq(typ: PType) = PSeqType(PReserved.implied(PKw.Seq), PGrouped.impliedBracket(typ))(NoPosition, NoPosition)
  def MakeMap(key: PType, value: PType) = PMapType(PReserved.implied(PKw.Map), PGrouped.impliedBracket(
      PPairArgument(key, PReserved.implied(PSym.Comma), value)(NoPosition, NoPosition)
    ))(NoPosition, NoPosition)
  def MakeMultiset(typ: PType) = PMultisetType(PReserved.implied(PKw.Multiset), PGrouped.impliedBracket(typ))(NoPosition, NoPosition)
}

///////////////////////////////////////////////////////////////////////////
// Identifiers (uses and definitions)

trait PIdentifier extends PLeaf {
  def name: String
  override def display = name
}

case class PIdnDef(name: String)(val pos: (Position, Position)) extends PNode with PIdentifier

trait PIdnUse extends PNode with PIdentifier with PIdnUseLsp {
  var decl: Option[PDeclaration] = None
  // Set for `x` when `x := ...`, set for `f` only when `x.f := ...`
  var assignUse: Boolean = false

  def rename(newName: String): PIdnUse
}
case class PIdnUseExp(name: String)(val pos: (Position, Position)) extends PIdnUse with PExp with PAssignTarget with PMaybeMacroExp with PLabelUse with PIdnUseExpLsp {
  override def possibleMacro = Some(this)
  override def macroArgs: Seq[PExp] = Seq()

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
case class PIdnRef(name: String)(val pos: (Position, Position)) extends PIdnUse {
  override def rename(newName: String) = PIdnRef(newName)(pos)
}

///////////////////////////////////////////////////////////////////////////
// Variable declarations

trait PAnyFormalArgDecl extends PNode with PUnnamedTypedDeclaration with PPrettySubnodes

case class PUnnamedFormalArgDecl(var typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl {
  override def pretty = typ.pretty
}

/** Any `var: Type` style binding, only useful during parsing and therefore not a `PNode`. */
case class PIdnTypeBinding(idndef: PIdnDef, c: PSym.Colon, typ: PType)(val pos: (Position, Position))

/** Anything that can be `PIdnUse`d as an expression (e.g. the receiver of a `PFieldAccess`). */
trait PAnyVarDecl extends PTypedDeclaration with PLocalDeclaration with PPrettySubnodes with PAnyVarDeclLsp {
  def toIdnUse: PIdnUseExp = {
    val use = PIdnUseExp(idndef.name)(idndef.pos)
    use.typ = typ
    use.decl = Some(this)
    use
  }
}
/** Anything that can be `PIdnUse`d as the target of a `PAssign`. */
trait PAssignableVarDecl extends PAnyVarDecl

/** Any argument to a method, function or predicate. */
case class PFormalArgDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl with PAnyVarDecl with PFormalArgDeclLsp
object PFormalArgDecl {
  def apply(d: PIdnTypeBinding): PFormalArgDecl = PFormalArgDecl(d.idndef, d.typ)(d.pos)
}
/** The return arguments of methods. */
case class PFormalReturnDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PAssignableVarDecl with PLocalDeclaration with PFormalReturnDeclLsp
object PFormalReturnDecl {
  def apply(d: PIdnTypeBinding): PFormalReturnDecl = PFormalReturnDecl(d.idndef, d.typ)(d.pos)
}
/** Any immutable variable binding, e.g. under quantifiers, let expressions.
 * [2014-11-13 Malte] Changed type to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PLogicalVarDecl(idndef: PIdnDef, var typ: PType)(val pos: (Position, Position)) extends PAnyVarDecl with PLocalDeclaration with PLogicalVarDeclLsp
object PLogicalVarDecl {
  def apply(d: PIdnTypeBinding): PLogicalVarDecl = PLogicalVarDecl(d.idndef, d.typ)(d.pos)
}
/** Declaration of a local variable. */
case class PLocalVarDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PAssignableVarDecl with PLocalDeclaration with PLocalVarDeclLsp
object PLocalVarDecl {
  def apply(d: PIdnTypeBinding): PLocalVarDecl = PLocalVarDecl(d.idndef, d.typ)(d.pos)
}
case class PFieldDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PTypedDeclaration with PGlobalDeclaration with PFieldDeclLsp {
  var decl: Option[PFields] = None
  override def annotations = decl.toSeq.flatMap(_.annotations)
  override def pretty = s"${idndef.pretty}: ${typ.pretty}"
}
object PFieldDecl {
  def apply(d: PIdnTypeBinding): PFieldDecl = PFieldDecl(d.idndef, d.typ)(d.pos)
}

///////////////////////////////////////////////////////////////////////////
// Types

trait PType extends PNode with PPrettySubnodes {
  def isUnknown: Boolean = this.isInstanceOf[PUnknown]
  def isValidOrUndeclared: Boolean
  def isGround: Boolean = true
  def substitute(ts: PTypeSubstitution): PType
  def subNodes: Seq[PType]

  //If we add type quantification or any type binders we need to modify this
  def freeTypeVariables: Set[String] =
    subNodes.flatMap(_.freeTypeVariables).toSet union
      (this match {
        case pdt: PDomainType if pdt.isTypeVar && PTypeVar.isFreePTVName(pdt.domain.name) => Set(pdt.genericName)
        case _ => Set()
      })
}


case class PPrimitiv[T <: PKeywordType](name: PReserved[T])(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType {
  override def isValidOrUndeclared = true
  override def substitute(ts: PTypeSubstitution): PType = this
  override val subNodes = Seq()

  override def pretty = name.pretty
}

case class PDomainType(domain: PIdnRef, args: Option[PDelimited.Comma[PSym.Bracket, PType]])(val pos: (Position, Position)) extends PGenericType with PDomainTypeLsp {
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
  override val subNodes = Seq()
  override def substitute(ts: PTypeSubstitution) = this
}

// for resolving if something cannot be typed
case class PUnknown()(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PInternalType {
  override def isValidOrUndeclared = false
  override def pretty = "<error>"
}

case class PWandType()(val pos: (Position, Position)) extends PInternalType {
  override def isValidOrUndeclared = true
  override def pretty = "Bool"
}

/** The type of a `PIdnUse` which refers to a function. Ensures that we get a
 * typecheck error if we try to use a function as a value.
 */
case class PFunctionType(argTypes: Seq[PType], resultType: PType) extends PType {
  override val pos: (Position, Position) = resultType.pos
  override def isValidOrUndeclared: Boolean = subNodes.forall(_.isValidOrUndeclared)
  override def substitute(ts: PTypeSubstitution): PType =
    PFunctionType(argTypes.map(_.substitute(ts)), resultType.substitute(ts))
  override def subNodes: Seq[PType] = argTypes ++ Seq(resultType)
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
  var brackets: Option[PGrouped[PSym.Paren, PExp]] = None
  var typ: PType = PUnknown()()

  def typeSubstitutions: scala.collection.Seq[PTypeSubstitution]

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

case class PTypeSubstitution(m: Map[String, PType]) //extends Map[String,PType]()
{
  require(m.values.forall(_.isValidOrUndeclared))

  def -(key: String) = new PTypeSubstitution(m.-(key))

  def get(key: String): Option[PType] = m.get(key)

  private def +(kv: (String, PType)): PTypeSubstitution = new PTypeSubstitution(m + kv)

  def iterator: Iterator[(String, PType)] = m.iterator

  def isDefinedAt(key: String) = contains(key)

  def keySet: Set[String] = m.keySet

  def restrict(s: Set[String]) = PTypeSubstitution(m.filter(s contains _._1))

  def map[B](f: ((String, PType)) => B): Seq[B] =
    m.map(f).toSeq

  def contains(key: PDomainType): Boolean = contains(key.domain.name)

  def contains(key: String): Boolean = get(key).nonEmpty

  def substitute(a: String, b: PType): PTypeSubstitution = {
    require(!contains(a))
    val ts = PTypeSubstitution(Map(a -> b))
    PTypeSubstitution(m.map(kv => kv._1 -> kv._2.substitute(ts)))
  }

  // The following methods all return a type substitution if successful,
  // otherwise a pair containing the expected and the found type.
  def *(other: PTypeSubstitution): Either[(PType, PType), PTypeSubstitution] =
    other.m.foldLeft(Right(this): Either[(PType, PType), PTypeSubstitution])({
      case (Right(s), p) => s.add(PTypeVar(p._1), p._2)
      case (l@Left(_), _) => l
    })

  def add(a: String, b: PType): Either[(PType, PType), PTypeSubstitution] = add(PTypeVar(a), b)

  def add(a: PType, b: PType): Either[(PType, PType), PTypeSubstitution] = {
    val as = a.substitute(this)
    val bs = b.substitute(this)
    (as, bs) match {
      case (aa, bb) if aa == bb => Right(this)
      case (PTypeVar(name), t) if PTypeVar.isFreePTVName(name) =>
        assert(!contains(name))
        Right(substitute(name, t) + (name -> t))
      case (_, PTypeVar(name)) if PTypeVar.isFreePTVName(name) => add(bs, as)
      case (gt1: PGenericType, gt2: PGenericType) if gt1.genericName == gt2.genericName =>
        val zippedArgs = gt1.typeArguments zip gt2.typeArguments
        (zippedArgs.foldLeft[Either[(PType, PType), PTypeSubstitution]](Right(this))
          ((ss: Either[(PType, PType), PTypeSubstitution], p: (PType, PType)) => ss match {
            case Right(sss) => sss.add(p._1, p._2) match {
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

  //  def apply(key:PDomainType) = apply(key.domain.name)
  //  def apply(key:String) = get(key)

  //  def getOrId(key:String) : String = this(key) match{ case Some(if (contains(key)) get(key) else key
  def this(s: Seq[(String, PType)]) = this(s.toMap)

  //  def this(m:Map[PDomainType,PType]) = this(m.map (kv=>kv._1.domain.name->kv._2))

  //  implicit def this(m:Map[String,PType]) = this(m.map (kv=>kv._1->kv._2))

  //  implicit def fromMap(m:Map[String,PType]) = new PTypeSubstitution(m)
  //  private def this() = this(Map())

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
  def opName: String
  def args: Seq[PExp]

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

case class PCall(func: PIdnRef, callArgs: PDelimited.Comma[PSym.Paren, PExp], typeAnnotated: Option[(PSym.Colon, PType)])(val pos: (Position, Position))
  extends PCallLike with PLocationAccess with PAccAssertion with PAssignTarget with PMaybeMacroExp with PCallLsp {
  override val idnuse = func
  override val opName = func.name
  override def possibleMacro = if (typeAnnotated.isEmpty) Some(idnuse) else None
  override def macroArgs = args
  override def loc = this
  override def perm = PFullPerm.implied()

  override def signatures: List[PTypeSubstitution] = (funcDecl match {
    case Some(pf: PFunction) if pf.formalArgs.size == args.size => List(
        (args.indices.map(i => POpApp.pArgS(i) -> pf.formalArgs(i).typ) :+ (POpApp.pResS -> pf.typ.resultType)).toMap
      )
    case Some(pdf: PDomainFunction) if pdf.formalArgs.size == args.size => List(
        (args.indices.map(i => POpApp.pArgS(i) -> pdf.formalArgs(i).typ.substitute(domainTypeRenaming.get)) :+
            (POpApp.pResS -> pdf.typ.resultType.substitute(domainTypeRenaming.get))).toMap
      )
    case Some(pp: PPredicate) if pp.formalArgs.size == args.size => List(
        (args.indices.map(i => POpApp.pArgS(i) -> pp.formalArgs(i).typ) :+ (POpApp.pResS -> Bool)).toMap
      )
    // this case is handled in Resolver.scala (- method check) which generates the appropriate error message
    case _ => Nil
  })

  var funcDecl: Option[PAnyFunction] = None
  var methodDecl: Option[PMethod] = None
  // def formalArgs: Option[Seq[PFormalArgDecl]] = decl.map(_.formalArgs)

  override def extraLocalTypeVariables = _extraLocalTypeVariables

  var _extraLocalTypeVariables: Set[PDomainType] = Set()
  var domainTypeRenaming: Option[PTypeRenaming] = None

  def isDomainFunction = domainTypeRenaming.isDefined
  def isPredicate = funcDecl.map(_.isInstanceOf[PPredicate]).getOrElse(false)

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

trait POpAppOperator extends POpApp with POpAppKeywordLsp {
  def ops: Seq[PReserved[POperator]]
  override def opName = ops.map(_.rs.operator).mkString
}

class PBinExp(val left: PExp, val op: PReserved[PBinaryOp], val right: PExp)(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(left, right)
  override val ops = Seq(op)

  override val extraLocalTypeVariables = if (op.rs.isInstanceOf[PCollectionOp]) Set(PCollectionOp.infVar) else Set()
  val signatures: List[PTypeSubstitution] = op.rs.signatures

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

case class PUnExp(op: PReserved[PUnaryOp], exp: PExp)(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(exp)
  override val ops = Seq(op)
  override val signatures = op.rs.signatures
}

case class PCondExp(cond: PExp, q: PSymOp.Question, thn: PExp, c: PSymOp.Colon, els: PExp)(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(cond, thn, els)
  override val ops = Seq(q, c)
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
  def idnuse: PIdnUse
}

case class PFieldAccess(rcv: PExp, dot: PSymOp.Dot, idnuse: PIdnRef)(val pos: (Position, Position)) extends POpApp with PLocationAccess with PAssignTarget {
  // TODO: Hover hint
  override final val args = Seq(rcv)
  override def opName = dot.rs.symbol

  override def signatures = idnuse.decl match {
    case Some(f: PFieldDecl) if f.typ.isValidOrUndeclared && rcv.typ.isValidOrUndeclared => List(
        Map(POpApp.pArgS(0) -> Ref, POpApp.pResS -> f.typ)
      )
    case _ => List()
  }
}

case class PUnfolding(unfolding: PKwOp.Unfolding, acc: PAccAssertion, in: PKwOp.In, exp: PExp)(val pos: (Position, Position)) extends POpAppOperator with PHeapOpApp {
  override val args = Seq(acc, exp)
  override def ops = Seq(unfolding, in)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)))
}

case class PApplying(applying: PKwOp.Applying, wand: PExp, in: PKwOp.In, exp: PExp)(val pos: (Position, Position)) extends POpAppOperator with PHeapOpApp {
  override val args = Seq(wand, exp)
  override def ops = Seq(applying, in)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)))
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

sealed trait PQuantifier extends PBinder with PScope {
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
case class PLet(l: PKwOp.Let, variable: PLogicalVarDecl, eq: PSymOp.EqEq, exp: PExp, in: PKwOp.In, nestedScope: PLetNestedScope)(val pos: (Position, Position)) extends POpAppOperator {
  override def args: Seq[PExp] = Seq(exp, nestedScope)
  override def ops = Seq(l, eq, in)

  // TODO:
  override def signatures = List(Map(POpApp.pResS -> POpApp.pArg(1)))
  // override def typeSubstitutions = (for (ts1 <- nestedScope.body.typeSubstitutions; ts2 <- exp.typeSubstitutions) yield (ts1 * ts2).toOption).flatten.toList.distinct
  // override def forceSubstitution(ts: PTypeSubstitution) = {
  //   exp.forceSubstitution(ts)
  //   variable.typ = exp.typ
  //   nestedScope.forceSubstitution(ts)
  // }
  override def forceSubstitution(ts: PTypeSubstitution) = {
    super.forceSubstitution(ts)
    variable.typ = exp.typ
  }
}

case class PLetNestedScope(body: PExp)(val pos: (Position, Position)) extends PNode with PBinder {
  var outerLet: PLet = null
  override val boundVars = Seq(outerLet.variable)
}

// [in,ex]
case class PInhaleExhaleExp(l: PSymOp.LBracket, in: PExp, c: PSymOp.Comma, ex: PExp, r: PSymOp.RBracket)(val pos: (Position, Position)) extends POpAppOperator with PHeapOpApp {
  override val args = Seq(in, ex)
  override def ops = Seq(l, c, r)

  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool)
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
  override def opName: String = op.rs.keyword
}

case class PCurPerm(op: PKwOp.Perm, res: PGrouped[PSym.Paren, PResourceAccess])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
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

case class PAccPred(op: PKwOp.Acc, amount: PGrouped[PSym.Paren, PMaybePairArgument[PLocationAccess, PExp]])(val pos: (Position, Position)) extends PCallKeyword with PAccAssertion {
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool))
  def loc = amount.inner.first
  def perm = amount.inner.second.map(_._2).getOrElse(PFullPerm.implied())
  override val args = Seq(loc, perm)
}

sealed trait PLabelUse extends PNode {
  def name: String
}
case class PLhsLabel(k: PKw.Lhs)(val pos: (Position, Position)) extends PNode with PLabelUse with PPrettySubnodes {
  override def name = k.rs.keyword
}

case class POldExp(op: PKwOp.Old, label: Option[PGrouped[PSym.Bracket, PLabelUse]], e: PGrouped[PSym.Paren, PExp])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(e.inner)
  override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))

  // override def getSemanticHighlights: Seq[SemanticHighlight] = label.toSeq.flatMap(RangePosition(_).map(sp => SemanticHighlight(sp, TokenType.Event)))
  // override def getHoverHints: Seq[HoverHint] = label.toSeq.flatMap(l => l.hoverHint(RangePosition(l)))
}

sealed trait PCollectionLiteral extends PCallKeyword {
  override def args: Seq[PExp] = callArgs.inner.toSeq
  def callArgs: PDelimited.Comma[PSym.Paren, PExp]
  def pElementType: PType

  def pCollectionType(pType: PType): PType

  def collectionName: String = opName
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
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSeq(pType)
}

case class PEmptySeq(op: PKwOp.Seq, pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PSeqLiteral with PEmptyCollectionLiteral

case class PExplicitSeq(op: PKwOp.Seq, callArgs: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PSeqLiteral with PExplicitCollectionLiteral

// [low..high)
case class PRangeSeq(l: PSymOp.LBracket, low: PExp, ds: PSymOp.DotDot, high: PExp, r: PSymOp.RParen)(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(low, high)
  override val ops = Seq(l, ds, r)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(Int)))
}

// base[idx]
case class PLookup(base: PExp, l: PSymOp.LBracket, idx: PExp, r: PSymOp.RBracket)(val pos: (Position, Position)) extends POpAppOperator {
  val keyType: PDomainType = POpApp.pArg(1)

  override val args = Seq(base, idx)
  override val ops = Seq(l, r)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(POpApp.pRes), POpApp.pArgS(1) -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, POpApp.pRes))
  )
}

case class PSeqSlice(seq: PExp, l: PSymOp.LBracket, s: Option[PExp], d: PSymOp.DotDot, e: Option[PExp], r: PSymOp.RBracket)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#Slice"
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

  override val opName = "update"
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

  override val opName = "size"
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
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSet(pType)
}

case class PEmptySet(op: PKwOp.Set, pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PSetLiteral with PEmptyCollectionLiteral

case class PExplicitSet(op: PKwOp.Set, callArgs: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral {
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeMultiset(pType)
}

case class PEmptyMultiset(op: PKwOp.Multiset, pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], callArgs: PDelimited.Comma[PSym.Paren, Nothing])(val pos: (Position, Position)) extends PMultiSetLiteral with PEmptyCollectionLiteral

case class PExplicitMultiset(op: PKwOp.Multiset, callArgs: PDelimited.Comma[PSym.Paren, PExp])(val pos: (Position, Position)) extends PMultiSetLiteral with PExplicitCollectionLiteral


/* ** Maps */

sealed trait PMapLiteral extends POpApp {
  override val opName = "Map#Map"
  override def args: Seq[PExp] = callArgs.inner.toSeq
  def callArgs: PDelimited.Comma[PSym.Paren, PExp]
  def pKeyType: PType
  def pValueType: PType

  def pMapType(keyType: PType, valueType: PType): PType =
    if (keyType.isUnknown || valueType.isUnknown) PUnknown()()
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
  override val opName = "Map#Maplet"
  override def args: Seq[PExp] = Seq(key, value)
  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> MakeMap(POpApp.pArg(0), POpApp.pArg(1))
  ))
}

case class PMapDomain(keyword: PKwOp.Domain, base: PGrouped[PSym.Paren, PExp])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#domain"
  override val args = Seq(base.inner)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(keyType)
  ))
}

case class PMapRange(keyword: PKwOp.Range, base: PGrouped[PSym.Paren, PExp])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#range"
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

case class PFold(fold: PKw.Fold, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PUnfold(unfold: PKw.Unfold, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PPackageWand(pckg: PKw.Package, e: PExp, proofScript: Option[PSeqn])(val pos: (Position, Position)) extends PStmt

case class PApplyWand(apply: PKw.Apply, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PExhale(exhale: PKw.Exhale, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PAssert(assert: PKw.Assert, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PAssume(assume: PKw.Assume, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PInhale(inhale: PKw.Inhale, e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

/** Can also represent a method call or statement macro with no `:=` when `targets` is empty. */
case class PAssign(targets: PDelimited[PAssignTarget, PSym.Comma], op: Option[PSymOp.Assign], rhs: PExp)(val pos: (Position, Position)) extends PStmt

sealed trait PIfContinuation extends PStmt
case class PIf(keyword: PReserved[PKeywordIf], cond: PExp, thn: PSeqn, els: Option[PIfContinuation])(val pos: (Position, Position)) extends PStmt with PIfContinuation
case class PElse(k: PKw.Else, els: PSeqn)(val pos: (Position, Position)) extends PStmt with PIfContinuation

case class PWhile(keyword: PKw.While, cond: PExp, invs: PDelimited[PSpecification[PKw.InvSpec], Option[PSym.Semi]], body: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PVars(keyword: PKw.Var, vars: PDelimited[PLocalVarDecl, PSym.Comma], init: Option[(PSymOp.Assign, PExp)])(val pos: (Position, Position)) extends PStmt {
  def assign: Option[PAssign] = init map (i => PAssign(vars.update(vars.toSeq.map(_.toIdnUse)), Some(i._1), i._2)(pos))
}

case class PLabel(label: PKw.Label, idndef: PIdnDef, invs: PDelimited[PSpecification[PKw.InvSpec], Option[PSym.Semi]])(val pos: (Position, Position)) extends PStmt with PLocalDeclaration {
  override def completionScope: Map[SuggestionScope,Byte] = Map(LabelScope -> 0, StatementScope -> -50)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Event
  override def tokenType = TokenType.Event
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Event
  override def hint = {
    val firstLine = s"${label.pretty} ${idndef.pretty}"
    val invsStr = invs.toSeq.map(i => s"\n  ${i.pretty}").mkString
    firstLine + invsStr
  }
  override def description: String = "Label"
}

case class PGoto(goto: PKw.Goto, target: PIdnUseExp)(val pos: (Position, Position)) extends PStmt with HasSemanticHighlights {
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(target).map(sp => SemanticHighlight(sp, TokenType.Event)).toSeq
  // override def getHoverHints: Seq[HoverHint] = target.hoverHint(RangePosition(target))
}

case class PTypeVarDecl(idndef: PIdnDef)(val pos: (Position, Position)) extends PLocalDeclaration with PPrettySubnodes {
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.TypeParameter
  override def hint: String = idndef.pretty
  override def completionScope: Map[SuggestionScope,Byte] = Map(TypeScope -> 0)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.TypeParameter
  override def completionChars: Option[Map[Char, Byte]] = Some(Map(':' -> 50))
  override def tokenType = TokenType.TypeParameter
  override def description: String = "Type Variable"
}

case class PSkip()(val pos: (Position, Position)) extends PStmt

case class PQuasihavoc(quasihavoc: PKw.Quasihavoc, lhs: Option[(PExp, PSymOp.Implies)], e: PExp)(val pos: (Position, Position)) extends PStmt

case class PQuasihavocall(quasihavocall: PKw.Quasihavocall, vars: PDelimited[PLogicalVarDecl, PSym.Comma], colons: PSym.ColonColon, lhs: Option[(PExp, PSymOp.Implies)], e: PExp)(val pos: (Position, Position)) extends PStmt with PScope

/* new(f1, ..., fn) or new(*) */
case class PNewExp(keyword: PKw.New, fields: PGrouped[PSym.Paren, Either[PSym.Star, PDelimited[PIdnUseExp, PSym.Comma]]])(val pos: (Position, Position)) extends PExp {
  override final val typeSubstitutions = Seq(PTypeSubstitution.id)
  def forceSubstitution(ts: PTypeSubstitution) = {}
  // override def getHoverHints: Seq[HoverHint] = fields.toSeq.flatMap(_.flatMap(ir => ir.hoverHint(RangePosition(ir))))
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

// Macros
sealed trait PMaybeMacroExp extends PExp {
  def possibleMacro: Option[PIdnUse]
  def macroArgs: Seq[PExp]
}

// Assignments
sealed trait PAssignTarget extends PExp

// Declarations

/** An entity is a declaration (named) or an error node */
sealed trait PEntity

trait PDeclaration extends PNode with PEntity with PDeclarationLsp {
  def idndef: PIdnDef
}

sealed trait PUnnamedTypedDeclaration extends PNode {
  def typ: PType
}

trait PGlobalDeclaration extends PDeclaration with PAnnotated with PGlobalDeclarationLsp

trait PLocalDeclaration extends PDeclaration with HasCompletionProposals

trait PUniversalDeclaration extends PDeclaration

sealed trait PTypedDeclaration extends PDeclaration with PUnnamedTypedDeclaration

case class PBracedExp(e: PGrouped[PSym.Brace, PExp])(val pos: (Position, Position)) extends PNode {
  override def pretty = s" ${e.l.pretty}\n  ${e.inner.pretty}\n${e.r.pretty}"
}

trait PGlobalCallable extends PGlobalDeclaration with HasFoldingRanges with HasSignatureHelps {
  def keyword: PReserved[_]
  def bodyRange: Option[RangePosition]
  def args: PDelimited.Comma[PSym.Paren, PAnyFormalArgDecl]
  def formalArgs: Seq[PAnyFormalArgDecl] = args.inner.toSeq
  def returnString: Option[String]
  def pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]]
  def posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]]
  override def hint: String = {
    val firstLine = s"${keyword.pretty} ${idndef.pretty}(${formalArgs.map(_.pretty).mkString(", ")})${returnString.getOrElse("")}"
    val contract = (pres.toSeq ++ posts.toSeq).map(_.pretty)
    val bodyString = bodyRange.map(_ => if (contract.length > 0) "\n{ ... }" else " { ... }").getOrElse("")
    s"$firstLine${contract.mkString}$bodyString"
  }
  override def getSignatureHelps: Seq[SignatureHelp] = {
    val bound = SelectionBoundKeyword(idndef.name)
    val start = SignatureHelpPart(false, s"${keyword.pretty} ${idndef.pretty}(", None)
    val args = formalArgs.map(fa => SignatureHelpPart(true, fa.pretty, None))
    val tail = SignatureHelpPart(false, ")" + returnString.getOrElse(""), None)
    def addCommas(args: Seq[SignatureHelpPart]): Seq[SignatureHelpPart] = if (args.length <= 1) args :+ tail else {
      args.head +: SignatureHelpPart(false, ", ", None) +: addCommas(args.drop(1))
    }
    val help = start +: addCommas(args)
    Seq(SignatureHelp(help, documentation, bound))
  }
  override def getFoldingRanges: Seq[FoldingRange] = {
    val thisRange = RangePosition(this).filter(rp => rp.start.line != rp._end.line)
    val bodyRangeFilter = bodyRange.filter(rp => rp.start.line != rp._end.line)
    val sameStart = thisRange.zip(bodyRangeFilter).map(rps => rps._1.start.line == rps._2.start.line).getOrElse(false)
    val ranges = if (sameStart) thisRange.toSeq else (thisRange.toSeq ++ bodyRangeFilter.toSeq)
    ranges.map(FoldingRange(_))
  }
  override def newText: Option[(String, InsertTextFormat.InsertTextFormat)] = {
    val args = formalArgs.zipWithIndex.map {
      case (ad: PFormalArgDecl, i) => s"$${${i+1}:${ad.idndef.pretty}}"
      case (_, i) => s"$${${i+1}:arg${i+1}}"
    }
    Some((s"${idndef.pretty}(${args.mkString(", ")})", InsertTextFormat.Snippet))
  }
}
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
trait PSingleMember extends PMember with PGlobalDeclaration {
  override def declares = Seq(this)
}

sealed trait PAnyFunction extends PSingleMember with PGlobalDeclaration with PTypedDeclaration with PGlobalCallable with HasSuggestionScopeRanges {
  override def tokenType = TokenType.Function
  override def symbolKind = SymbolKind.Function
  override def returnString: Option[String] = Some(s": ${resultType.pretty}")
  // override def getGotoDefinitions: Seq[GotoDefinition] = super.getGotoDefinitions ++ formalArgs.map(_.getGotoDefinitions)

  def resultType: PType
  override def typ: PFunctionType = PFunctionType(formalArgs.map(_.typ), resultType)

  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(this).map(SuggestionScopeRange(_, CallableSignatureScope)).toSeq ++
    bodyRange.map(SuggestionScopeRange(_, ExpressionScope)).toSeq
  override def completionScope: Map[SuggestionScope,Byte] = Map(ExpressionScope -> 0, StatementScope -> -50)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Function
}

///////////////////////////////////////////////////////////////////////////
// Program Members

case class PProgram(imports: Seq[PImport], macros: Seq[PDefine], domains: Seq[PDomain], fields: Seq[PFields], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod], extensions: Seq[PExtender], errors: Seq[ParseReport])(val pos: (Position, Position)) extends PNode with PProgramLsp {
  override def pretty =  {
    val all = Seq(imports, macros, domains, fields, functions, predicates, methods, extensions).filter(_.length > 0)
    all.map(_.map(_.pretty).mkString("\n")).mkString("\n")
  }
}

case class PImport(annotations: Seq[PAnnotation], imprt: PKw.Import, file: PStringLiteral)(val pos: (Position, Position)) extends PNode with PPrettySubnodes with PLspDocumentSymbol {
  var local: Boolean = true
  var resolved: Option[Path] = None
  override def getSymbol: Option[DocumentSymbol] = (RangePosition(this), RangePosition(file), resolved) match {
    case (Some(tp), Some(fp), Some(resolved)) =>
      // We avoid any circular dependencies since `resolved` is only set for imports which caused a
      // file to actually be imported.
      Some(DocumentSymbol(resolved.getFileName.toString(), None, tp, fp, SymbolKind.File, Nil, Some(resolved)))
    case _ => None
  }
}

case class PDefine(annotations: Seq[PAnnotation], define: PKw.Define, idndef: PIdnDef, parameters: Option[PDelimited.Comma[PSym.Paren, PIdnDef]], body: PNode)(val pos: (Position, Position)) extends PSingleMember with PStmt with PAnnotated with PGlobalDeclaration {
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Function
  override def hint: String = {
    val params = parameters.map(_.pretty).getOrElse("")
    s"${define.pretty} ${idndef.pretty}$params"
  }
  override def completionScope: Map[SuggestionScope,Byte] = body match {
    case _: PExp => Map(ExpressionScope -> 0, TypeScope -> 0, StatementScope -> -50)
    case _: PStmt => Map(StatementScope -> 0)
    case _ => Map(MemberScope -> -50)
  }
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Snippet
  override def tokenType = TokenType.Macro
  override def description: String = "Macro"
}

case class PDomain(annotations: Seq[PAnnotation], domain: PKw.Domain, idndef: PIdnDef, typVars: Option[PDelimited.Comma[PSym.Bracket, PTypeVarDecl]], interpretations: Option[PDomainInterpretations], members: PGrouped[PSym.Brace, PDomainMembers])
                  (val pos: (Position, Position)) extends PSingleMember with PGlobalDeclaration with PPrettySubnodes with HasFoldingRanges with HasSuggestionScopeRanges {
  def typVarsSeq: Seq[PTypeVarDecl] = typVars.map(_.inner.toSeq).getOrElse(Nil)

  override def tokenType = TokenType.Interface
  override def symbolKind = SymbolKind.Interface
  override def hint = {
    val tvsStr = typVars.map(_.inner.toSeq.map(_.idndef.pretty).mkString("[", ",", "]")).getOrElse("")
    s"${domain.pretty} ${idndef.pretty}$tvsStr"
  }
  override def getFoldingRanges: Seq[FoldingRange] = RangePosition(members).map(FoldingRange(_)).toSeq
  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(members).map(SuggestionScopeRange(_, DomainScope)).toSeq
  override def completionScope: Map[SuggestionScope,Byte] = Map(TypeScope -> 0)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Interface
  override def completionChars: Option[Map[Char, Byte]] = Some(Map(':' -> 50))
  override def description: String = "Domain"
}

case class PDomainFunctionInterpretation(k: PKw.Interpretation, i: PStringLiteral)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty = s"\n  ${super.pretty}"
}
case class PDomainFunction(annotations: Seq[PAnnotation], unique: Option[PKw.Unique], function: PKw.Function, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PAnyFormalArgDecl], c: PSym.Colon, resultType: PType, interpretation: Option[PDomainFunctionInterpretation])
                          (val domainName: PIdnRef)(val pos: (Position, Position)) extends PAnyFunction with PPrettySubnodes {

  override def keyword = function
  override def pres = PDelimited.empty
  override def posts = PDelimited.empty
  override def bodyRange: Option[RangePosition] = None
  override def description: String = "Domain Function"
}

case class PAxiom(annotations: Seq[PAnnotation], axiom: PKw.Axiom, idndef: Option[PIdnDef], exp: PBracedExp)(val domainName: PIdnRef)(val pos: (Position, Position)) extends PScope with PPrettySubnodes with HasFoldingRanges {

  override def getFoldingRanges: Seq[FoldingRange] = RangePosition(exp).map(FoldingRange(_)).toSeq
}
case class PDomainMembers(funcs: PDelimited[PDomainFunction, Option[PSym.Semi]], axioms: PDelimited[PAxiom, Option[PSym.Semi]])(val pos: (Position, Position)) extends PNode {
  override def pretty: String = {
    val fPretty = if (funcs.length == 0) "" else s"\n  ${funcs.prettyLines.replace("\n", "\n  ")}\n"
    val aPretty = if (axioms.length == 0) "" else s"\n  ${axioms.prettyLines.replace("\n", "\n  ")}\n"
    s"${fPretty}${aPretty}"
  }
}

case class PDomainInterpretation(name: String, c: PSym.Colon, str: PStringLiteral)(val pos: (Position, Position)) extends PNode with PPrettySubnodes
case class PDomainInterpretations(k: PReserved[PKeywordLang], m: PDelimited.Comma[PSym.Paren, PDomainInterpretation])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  def interps: Map[String, String] = m.inner.toSeq.map(i => i.name -> i.str.grouped.inner).toMap
}

trait PDomainMember1 extends PNode with PPrettySubnodes
case class PDomainFunction1(annotations: Seq[PAnnotation], unique: Option[PKw.Unique], function: PKw.Function, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PAnyFormalArgDecl], c: PSym.Colon, typ: PType, interpretation: Option[PDomainFunctionInterpretation], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PDomainMember1
case class PAxiom1(annotations: Seq[PAnnotation], axiom: PKw.Axiom, idndef: Option[PIdnDef], exp: PBracedExp, s: Option[PSym.Semi])(val pos: (Position, Position)) extends PDomainMember1
case class PDomainMembers1(members: Seq[PDomainMember1])(val pos: (Position, Position)) extends PNode with PPrettySubnodes


case class PFields(annotations: Seq[PAnnotation], field: PKw.Field, fields: PDelimited[PFieldDecl, PSym.Comma], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PMember with PPrettySubnodes {
  override def declares: Seq[PGlobalDeclaration] = fields.toSeq
}

case class PSpecification[+T <: PKw.Spec](k: PReserved[PKw.Spec], e: PExp)(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty: String = "\n  " + super.pretty
}

case class PFunction(annotations: Seq[PAnnotation], function: PKw.Function, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], c: PSym.Colon, resultType: PType, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]], posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]], body: Option[PBracedExp])
                    (val pos: (Position, Position)) extends PAnyFunction with PGlobalCallableNamedArgs with PPrettySubnodes {
  def deepCopy(annotations: Seq[PAnnotation] = this.annotations, function: PKw.Function = this.function, idndef: PIdnDef = this.idndef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl] = this.args, c: PSym.Colon = this.c, resultType: PType = this.resultType, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]] = this.pres, posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]] = this.posts, body: Option[PBracedExp] = this.body): PFunction = {
    StrategyBuilder.Slim[PNode]({
      case p: PFunction => PFunction(annotations, function, idndef, args, c, resultType, pres, posts, body)(p.pos)
    }).execute[PFunction](this)
  }

  override def keyword = function
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
  override def description: String = "Function"
}

case class PPredicate(annotations: Seq[PAnnotation], predicate: PKw.Predicate, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], body: Option[PBracedExp])(val pos: (Position, Position))
  extends PAnyFunction with PGlobalCallableNamedArgs with PPrettySubnodes {
  override def resultType = Bool

  override def returnString: Option[String] = None

  override def tokenType = TokenType.Struct
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Struct
  override def keyword = predicate
  override def pres = PDelimited.empty
  override def posts = PDelimited.empty
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Struct
  override def description: String = "Predicate"
}

case class PMethod(annotations: Seq[PAnnotation], method: PKw.Method, idndef: PIdnDef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl], returns: Option[PMethodReturns], pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]], posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]], body: Option[PStmt])
                  (val pos: (Position, Position)) extends PSingleMember with PGlobalDeclaration with PGlobalCallableNamedArgs with PPrettySubnodes with HasSuggestionScopeRanges {
  def deepCopy(annotations: Seq[PAnnotation] = this.annotations, method: PKw.Method = this.method, idndef: PIdnDef = this.idndef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl] = this.args, returns: Option[PMethodReturns] = this.returns, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]] = this.pres, posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]] = this.posts, body: Option[PStmt] = this.body): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(annotations, method, idndef, args, returns, pres, posts, body)(p.pos)
    }).execute[PMethod](this)
  }

  def deepCopyWithNameSubstitution(annotations: Seq[PAnnotation] = this.annotations, method: PKw.Method = this.method, idndef: PIdnDef = this.idndef, args: PDelimited.Comma[PSym.Paren, PFormalArgDecl] = this.args, returns: Option[PMethodReturns] = this.returns, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]] = this.pres, posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]] = this.posts, body: Option[PStmt] = this.body)
                                  (idn_generic_name: String, idn_substitution: String): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(annotations, method, idndef, args, returns, pres, posts, body)(p.pos)
      case p@PIdnDef(name) if name == idn_generic_name => PIdnDef(idn_substitution)(p.pos)
      case p@PIdnUseExp(name) if name == idn_generic_name => PIdnUseExp(idn_substitution)(p.pos)
      case p@PIdnRef(name) if name == idn_generic_name => PIdnRef(idn_substitution)(p.pos)
    }).execute[PMethod](this)
  }
  def formalReturns: Seq[PFormalReturnDecl] = returns.map(_.formalReturns.inner.toSeq).getOrElse(Nil)

  override def keyword = method
  override def tokenType = TokenType.Method
  override def symbolKind = SymbolKind.Method
  override def returnString: Option[String] = Some(s" returns (${returns.toSeq.flatMap(_.formalReturns.inner.toSeq.map(_.hint)).mkString(", ")})")
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(this).map(SuggestionScopeRange(_, CallableSignatureScope)).toSeq ++
    bodyRange.map(SuggestionScopeRange(_, StatementScope)).toSeq
  override def completionScope: Map[SuggestionScope,Byte] = Map(StatementScope -> 0, ExpressionScope -> -20)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Method
  override def typeHint: Option[String] = {
    val args = formalArgs.map(_.typ.pretty).mkString("(", ", ", ")")
    val rets = returns.toSeq.flatMap(_.formalReturns.inner.toSeq.map(_.typ.pretty)).mkString("(", ", ", ")")
    Some(s"$args returns $rets")
  }
  override def description: String = "Method"
}

case class PMethodReturns(k: PKw.Returns, formalReturns: PGrouped[PSym.Paren, PDelimited[PFormalReturnDecl, PSym.Comma]])(val pos: (Position, Position)) extends PNode with PPrettySubnodes

/**
  * Used for parsing annotation for top level members. Passed as an argument to the members to construct them.
  */
case class PAnnotationsPosition(annotations: Seq[PAnnotation], pos: (Position, Position))

case class PAnnotation(at: PSym.At, key: PAnnotationKey, values: PGrouped[PSym.Paren, PDelimited[PStringLiteral, PSym.Comma]])(val pos: (Position, Position)) extends PNode with PPrettySubnodes with PAnnotationLsp {
  override def pretty: String = super.pretty + "\n"
}

case class PAnnotationKey(name: String)(val pos: (Position, Position)) extends PNode with PPrettySubnodes with PLeaf {
  override def display: String = name
}

case class PStringLiteral(grouped: PGrouped[_, String])(val pos: (Position, Position)) extends PNode with PLeaf with PStringLiteralLsp {
  override def display: String = s"${grouped.l.pretty}${grouped.inner}${grouped.r.pretty}"
}

/**
  * A entity represented by names for whom we have seen more than one
  * declaration so we are unsure what is being represented.
  */
case class PMultipleEntity() extends PErrorEntity {
  val name = "multiple"
}

/**
  * An unknown entity, represented by names whose declarations are missing.
  */
case class PUnknownEntity() extends PErrorEntity {
  val name = "unknown"
}


trait PExtender extends PNode {
  def typecheck(t: TypeChecker, n: NameAnalyser): Option[Seq[String]] = ???

  def typecheck(t: TypeChecker, n: NameAnalyser, expected: PType): Option[Seq[String]] = ???

  def namecheck(n: NameAnalyser): Nothing = ???

  def translateMemberSignature(t: Translator): Member = ???

  def translateMember(t: Translator): Member = ???

  def translateStmt(t: Translator): Stmt = ???

  def translateExp(t: Translator): Exp = ???

  def translateType(t: Translator): Type = ???

  def transformExtension(t: Transformer.type): PNode = ???
}
