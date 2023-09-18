// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder}
import viper.silver.ast.{Exp, MagicWandOp, Member, NoPosition, Position, Stmt, Type}
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
  def subnodes: Seq[PNode] = PNode.children(this).flatMap(PNode.nodes).toSeq

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

  /** @see [[Transformer.transform()]] */
  def transform(pre: PartialFunction[PNode, PNode] = PartialFunction.empty)
               (recursive: PNode => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[PNode, PNode] = PartialFunction.empty,
                allowChangingNodeType: Boolean = false,
                resultCheck: PartialFunction[(PNode, PNode), Unit] = PartialFunction.empty)
  : this.type =

    Transformer.transform[this.type](this, pre)(recursive, post, allowChangingNodeType, resultCheck)

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
    var prev: PNode = null


    def setNodeChildConnections(node: Any): Unit =
      node match {
        case c: PNode =>
          c.parent = Some(this)
          _children += c
          c.index = ind
          ind += 1
          c.prev = Some(prev)
          c.next = null
          if (prev != null)
            prev.next = Some(c)
          prev = c
          c.initProperties()
        case _ =>
          for (c <- PNode.children(node))
            setNodeChildConnections(c)
      }

    _children.clear()
    for (c <- PNode.children(this))
      setNodeChildConnections(c)

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
    case _ => this.subnodes.map(_.pretty).mkString("")
  }
}

object PNode {
  def children(n: Any): Iterator[Any] = {
    n match {
      case _: PLeaf | _: Unit => Iterator.empty
      case t: PExtender => t.getSubnodes().iterator
      // Includes `Option`, `Seq`, etc.
      case i: IterableOnce[_] => i.iterator
      // Includes `Either`, all case classes, etc.
      case t: Product => t.productIterator
      // This case should be avoided by marking your node as a `PLeaf`.
      case _ => sys.error(s"Unexpected node type: ${n.getClass}")
    }
  }
  def nodes(n: Any): Iterator[PNode] = {
    n match {
      case n: PNode => Iterator(n)
      case _ => children(n).flatMap(nodes)
    }
  }
  def callSubnodes(n: PNode): Seq[PNode] = n.subnodes
}

object TypeHelper {
  val Int = PPrimitiv(PReserved(PKw.Int)(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Bool = PPrimitiv(PReserved(PKw.Bool)(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Perm = PPrimitiv(PReserved(PKw.Perm)(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Ref = PPrimitiv(PReserved(PKw.Ref)(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Wand = PWandType()((NoPosition, NoPosition))
  def MakeSet(typ: PType) = PSetType(PReserved(PKw.Set)(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
  def MakeSeq(typ: PType) = PSeqType(PReserved(PKw.Seq)(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
  def MakeMap(key: PType, value: PType) = PMapType(PReserved(PKw.Map)(NoPosition, NoPosition), key, value)((NoPosition, NoPosition))
  def MakeMultiset(typ: PType) = PMultisetType(PReserved(PKw.Multiset)(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
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
  override def prettyNoBrackets: String = name
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

case class PDomainType(domain: PIdnRef, args: Option[PSym.Punctuated[PSym.Bracket, PType]])(val pos: (Position, Position)) extends PGenericType with PDomainTypeLsp {
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
    if (s.length == 0 && args.isEmpty) this else copy(args = Some(args.get.update(args.get.inner.update(s))))(pos)
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

  def freshTypeSubstitution(tvns: Seq[String]): PTypeRenaming = {
    val ind = lastIndex.getAndIncrement()
    new PTypeRenaming((tvns map (tv => tv -> getFreshName(tv, ind))).toMap)
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
  def elementType: PType

  override val typeArguments = Seq(elementType)
  override val subNodes = Seq(elementType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)
}

case class PSeqType(seq: PReserved[PKw.Seq.type], elementType: PGrouped[PSym.Bracket, PType])(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Seq"

  override def substitute(map: PTypeSubstitution) = PSeqType(seq, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PSetType(set: PReserved[PKw.Set.type], elementType: PGrouped[PSym.Bracket, PType])(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Set"

  override def substitute(map: PTypeSubstitution) = PSetType(set, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PMultisetType(multiset: PReserved[PKw.Multiset.type], elementType: PGrouped[PSym.Bracket, PType])(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"

  override def substitute(map: PTypeSubstitution) = PMultisetType(multiset, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMultisetType = copy(elementType = s.head)(pos)
}

case class PMapType(map: PReserved[PKw.Map.type], typ: PGrouped[PSym.Bracket, PPairArgument[PType, PType]])(val pos: (Position, Position)) extends PType with PGenericType {
  override val genericName = "Map"
  def keyType = typ.inner.first
  def valueType = typ.inner.second
  override val subNodes = Seq(keyType, valueType)
  override val typeArguments = Seq(keyType, valueType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)

  override def substitute(map: PTypeSubstitution) = PMapType(this.map, keyType.substitute(map), valueType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMapType = copy(keyType = s.head, valueType = s(1))(pos)
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
  override def prettyNoBrackets = e.pretty
}

class PTypeSubstitution(val m: Map[String, PType]) //extends Map[String,PType]()
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
  override def args = args.toSeq
  def callArgs: PSym.Punctuated[PSym.Paren, PExp]
}

case class PCall(func: PIdnRef, callArgs: PSym.Punctuated[PSym.Paren, PExp], typeAnnotated: Option[(PSym.Colon, PType)])(val pos: (Position, Position))
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

  // override def prettyNoBrackets = {
  //   val call = s"$opName${args.map(_.pretty).mkString("(", ", ", ")")}"
  //   typeAnnotated match {
  //     case None => call
  //     case Some(tp) => s"$call: ${tp.pretty}"
  //   }
  // }
}

class PBinExp(val left: PExp, val op: PReserved[PBinaryOp], val right: PExp)(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(left, right)
  override val ops = Seq(op)

  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    op.rs match {
      case PSymOp.Append | PKwOp.Union | PKwOp.Intersection | PKwOp.Setminus | PKwOp.Subset | PKwOp.In => Set(extraElementType)
      case _ => Set()
    }
  // TODO: move this to `op.rs.signatures`
  val signatures: List[PTypeSubstitution] = op.rs match {
    case PSymOp.Plus | PSymOp.Minus => List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int)
    )
    case PSymOp.Mul => List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int)
    )
    case PSymOp.Div => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int)
    )
    case PSymOp.ArithDiv | PSymOp.Mod => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int))
    case PSymOp.Lt | PSymOp.Le | PSymOp.Gt | PSymOp.Ge => List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Bool)
    )
    case PSymOp.EqEq | PSymOp.Ne => List(
      Map(POpApp.pArgS(1) -> POpApp.pArg(0), POpApp.pResS -> Bool))
    case PSymOp.AndAnd | PSymOp.OrOr | PSymOp.Iff | PSymOp.Implies => List(
      Map(POpApp.pArgS(1) -> Bool, POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool))
    case PSymOp.Wand => List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Wand),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Wand, POpApp.pResS -> Wand),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Wand, POpApp.pResS -> Bool))
    case PKwOp.In => List(
      Map(POpApp.pArgS(1) -> MakeSet(POpApp.pArg(0)), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> MakeSeq(POpApp.pArg(0)), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> MakeMultiset(POpApp.pArg(0)), POpApp.pResS -> Int),
      Map(POpApp.pArgS(1) -> MakeMap(POpApp.pArg(0), extraElementType), POpApp.pResS -> Bool)
    )
    case PSymOp.Append => List(
      Map(POpApp.pArgS(0) -> MakeSeq(extraElementType), POpApp.pArgS(1) -> MakeSeq(extraElementType), POpApp.pResS -> MakeSeq(extraElementType))
    )
    case PKwOp.Union | PKwOp.Intersection | PKwOp.Setminus => List(
      Map(POpApp.pArgS(0) -> MakeSet(extraElementType), POpApp.pArgS(1) -> MakeSet(extraElementType), POpApp.pResS -> MakeSet(extraElementType)),
      Map(POpApp.pArgS(0) -> MakeMultiset(extraElementType), POpApp.pArgS(1) -> MakeMultiset(extraElementType), POpApp.pResS -> MakeMultiset(extraElementType))
    )
    case PKwOp.Subset => List(
      Map(POpApp.pArgS(0) -> MakeSet(extraElementType), POpApp.pArgS(1) -> MakeSet(extraElementType), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> MakeMultiset(extraElementType), POpApp.pArgS(1) -> MakeMultiset(extraElementType), POpApp.pResS -> Bool)
    )
    case other => sys.error(s"internal error - unknown binary operator \"${other.operator}\"")
  }

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
}

object PBinExp {
  def apply(left: PExp, op: PReserved[PBinaryOp], right: PExp)(pos: (Position, Position)): PBinExp =
    new PBinExp(left, op, right)(pos)

  def unapply(arg: PBinExp): Option[(PExp, PReserved[PBinaryOp], PExp)] = Some(arg.left, arg.op, arg.right)
}

case class PMagicWandExp(override val left: PExp, wand: PReserved[PSymOp.Wand.type], override val right: PExp)(val posi: (Position, Position)) extends PBinExp(left, wand, right)(posi) with PResourceAccess

case class PUnExp(op: PReserved[PUnaryOp], exp: PExp)(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(exp)
  override val ops = Seq(op)
  override val signatures: List[PTypeSubstitution] = op.rs match {
    case PSymOp.Minus => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pResS -> Int),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pResS -> Perm)
    )
    case PSymOp.Not => List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool)
    )
    case other => sys.error(s"internal error - unknown unary operator ${other.operator}")
  }
  override def separator = ""
}

case class PCondExp(cond: PExp, q: PReserved[PSymOp.Question.type], thn: PExp, c: PReserved[PSymOp.Colon.type], els: PExp)(val pos: (Position, Position)) extends POpAppOperator {
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
  override def prettyNoBrackets = keyword.pretty
}

case class PIntLit(i: BigInt)(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Int
  override def prettyNoBrackets = i.toString()
}

case class PResultLit(result: PReserved[PKw.Result.type])(val pos: (Position, Position)) extends PSimpleLiteral {
  override def prettyNoBrackets = result.pretty
}

case class PBoolLit(keyword: PReserved[PKeywordConstant], b: Boolean)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Bool
}

case class PNullLit(keyword: PReserved[PKw.Null.type])(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Ref
}

sealed trait PHeapOpApp extends POpApp

sealed trait PResourceAccess extends PHeapOpApp

trait PLocationAccess extends PResourceAccess {
  def idnuse: PIdnUse
}

case class PFieldAccess(rcv: PExp, dot: PReserved[PSymOp.Dot.type], idnuse: PIdnRef)(val pos: (Position, Position)) extends POpApp with PLocationAccess with PAssignTarget {
  // TODO: Hover hint
  override final val args = Seq(rcv)
  override def opName = dot.rs.symbol

  override def signatures = idnuse.decl match {
    case Some(f: PFieldDecl) if f.typ.isValidOrUndeclared && rcv.typ.isValidOrUndeclared => List(
        Map(POpApp.pArgS(0) -> Ref, POpApp.pResS -> f.typ)
      )
    case _ => List()
  }
  override def prettyNoBrackets = s"${rcv.pretty}${dot.pretty}${idnuse.pretty}"
}

case class PUnfolding(unfolding: PReserved[PKwOp.Unfolding.type], acc: PAccAssertion, in: PReserved[PKwOp.In.type], exp: PExp)(val pos: (Position, Position)) extends POpAppOperator with PHeapOpApp {
  override val args = Seq(acc, exp)
  override def ops = Seq(unfolding, in)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)))
}

case class PApplying(applying: PReserved[PKwOp.Applying.type], wand: PExp, in: PReserved[PKwOp.In.type], exp: PExp)(val pos: (Position, Position)) extends POpAppOperator with PHeapOpApp {
  override val args = Seq(wand, exp)
  override def ops = Seq(applying, in)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Wand, POpApp.pResS -> POpApp.pArg(1)))
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

case class PTrigger(exp: PSym.Punctuated[PSym.Brace, PExp])(val pos: (Position, Position)) extends PNode with PPrettySubnodes {
  override def pretty = exp.pretty
}

sealed trait PQuantifier extends PBinder with PScope {
  def keyword: PReserved[PKeywordLang]
  def c: PReserved[PSym.ColonColon.type]
  def vars: Seq[PLogicalVarDecl]
  def triggers: Seq[PTrigger]
  override def boundVars = vars
  override def prettyNoBrackets = {
    val varsStr = vars.map(_.pretty).mkString(", ")
    val triggersStr = triggers.map(_.pretty + " ").mkString
    s"${keyword.pretty} $varsStr ${c.pretty} $triggersStr${body.pretty}"
  }
}

case class PExists(keyword: PReserved[PKw.Exists.type], vars: PDelimited[PLogicalVarDecl, PSym.Comma], c: PReserved[PSym.ColonColon.type], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForall(keyword: PReserved[PKw.Forall.type], vars: PDelimited[PLogicalVarDecl, PSym.Comma], c: PReserved[PSym.ColonColon.type], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForPerm(keyword: PReserved[PKw.Forperm.type], vars: PDelimited[PLogicalVarDecl, PSym.Comma], accessRes: PGrouped[PSym.Bracket, PResourceAccess], c: PReserved[PSym.ColonColon.type], body: PExp)(val pos: (Position, Position)) extends PQuantifier {
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
case class PLet(l: PReserved[PKwOp.Let.type], variable: PLogicalVarDecl, eq: PReserved[PSymOp.EqEq.type], exp: PExp, in: PReserved[PKwOp.In.type], nestedScope: PLetNestedScope)(val pos: (Position, Position)) extends POpAppOperator {
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

  override def prettyNoBrackets = body.prettyNoBrackets
  override val boundVars = Seq(outerLet.variable)
}

// [in,ex]
case class PInhaleExhaleExp(l: PReserved[PSymOp.LBracket.type], in: PExp, c: PReserved[PSymOp.Comma.type], ex: PExp, r: PReserved[PSymOp.RBracket.type])(val pos: (Position, Position)) extends POpAppOperator with PHeapOpApp {
  override val args = Seq(in, ex)
  override def ops = Seq(l, c, r)
  override def separator: String = ""

  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool)
  )
}

case class PNoPerm(keyword: PReserved[PKw.None.type])(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PFullPerm(keyword: PReserved[PKw.Write.type])(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}
object PFullPerm {
  def implied(): PFullPerm = PFullPerm(PReserved(PKw.Write)(NoPosition, NoPosition))(NoPosition, NoPosition)
}

case class PWildcard(keyword: PReserved[PKw.Wildcard.type])(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PEpsilon(keyword: PReserved[PKw.Epsilon.type])(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

trait PCallKeyword extends POpApp {
  def op: PReserved[POperatorKeyword]
  override def opName: String = op.rs.keyword
}

case class PCurPerm(op: PReserved[PKwOp.Perm.type], res: PGrouped[PSym.Paren, PResourceAccess])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(res.inner)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> Perm)
  )
}

case class PPairArgument[+T, +U](first: T, c: PSym.Comma, second: U)(val pos: (Position, Position)) extends PNode
case class PMaybePairArgument[+T, +U](first: T, second: Option[(PSym.Comma, U)])(val pos: (Position, Position)) extends PNode

sealed trait PAccAssertion extends PExp {
  def loc: PLocationAccess
  def perm: PExp
}

case class PAccPred(op: PReserved[PKwOp.Acc.type], amount: PGrouped[PSym.Paren, PMaybePairArgument[PLocationAccess, PExp]])(val pos: (Position, Position)) extends PCallKeyword with PAccAssertion {
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool))
  def loc = amount.inner.first
  def perm = amount.inner.second.map(_._2).getOrElse(PFullPerm.implied())
  override val args = Seq(loc, perm)
}

sealed trait PLabelUse extends PExp {
  def name: String
  override def prettyNoBrackets = name
}
case class PLhsLabel(k: PReserved[PKw.Lhs.type])(val pos: (Position, Position)) extends PNode with PLabelUse {
  override def name = k.rs.keyword
}

case class POldExp(op: PReserved[PKwOp.Old.type], label: Option[PGrouped[PSym.Bracket, PLabelUse]], e: PGrouped[PSym.Paren, PExp])(val pos: (Position, Position)) extends PCallKeyword with PHeapOpApp {
  override val args = Seq(e.inner)
  override val signatures: List[PTypeSubstitution] = List(Map(POpApp.pResS -> POpApp.pArg(0)))

  // override def getSemanticHighlights: Seq[SemanticHighlight] = label.toSeq.flatMap(RangePosition(_).map(sp => SemanticHighlight(sp, TokenType.Event)))
  // override def getHoverHints: Seq[HoverHint] = label.toSeq.flatMap(l => l.hoverHint(RangePosition(l)))
}

sealed trait PCollectionLiteral extends PCallKeyword {
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

  override val args = Seq()
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

case class PEmptySeq(op: PReserved[PKwOp.Seq.type], pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], unit: PGrouped[PSym.Paren, Unit])(val pos: (Position, Position)) extends PSeqLiteral with PEmptyCollectionLiteral

case class PExplicitSeq(op: PReserved[PKwOp.Seq.type], args: PSym.Punctuated[PSym.Paren, PExp])(val pos: (Position, Position)) extends PSeqLiteral with PExplicitCollectionLiteral

// [low..high)
case class PRangeSeq(l: PReserved[PSymOp.LBracket.type], low: PExp, ds: PReserved[PSymOp.DotDot.type], high: PExp, r: PReserved[PSymOp.RParen.type])(val pos: (Position, Position)) extends POpAppOperator {
  override val args = Seq(low, high)
  override val ops = Seq(l, ds, r)
  override val separator = ""

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(Int)))
}

// base[idx]
case class PLookup(base: PExp, l: PReserved[PSymOp.LBracket.type], idx: PExp, r: PReserved[PSymOp.RBracket.type])(val pos: (Position, Position)) extends POpAppOperator {
  val keyType: PDomainType = POpApp.pArg(1)

  override val args = Seq(base, idx)
  override val ops = Seq(l, r)
  override val separator = ""
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(POpApp.pRes), POpApp.pArgS(1) -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, POpApp.pRes))
  )
}

case class PSeqSlice(seq: PExp, l: PReserved[PSymOp.LBracket.type], s: Option[PExp], d: PReserved[PSymOp.DotDot.type], e: Option[PExp], r: PReserved[PSymOp.RBracket.type])(val pos: (Position, Position)) extends POpApp {
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

  override def prettyNoBrackets = s"${seq.pretty}${l.pretty}${s.map(_.pretty).getOrElse("")}${d.pretty}${e.map(_.pretty).getOrElse("")}${r.pretty}"
}

case class PUpdate(base: PExp, l: PReserved[PSymOp.LBracket.type], key: PExp, a: PReserved[PSymOp.Assign.type], value: PExp, r: PReserved[PSymOp.RBracket.type])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)
  val elementType: PDomainType = POpApp.pArg(2)

  override val opName = "update"
  override val args = Seq(base, key, value)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, elementType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(elementType), POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(elementType)),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, elementType), POpApp.pResS -> MakeMap(keyType, elementType))
  )

  override def prettyNoBrackets = s"${base.pretty}[${key.pretty} := ${value.pretty}]"
}

case class PSize(l: PReserved[PSymOp.Or.type], seq: PExp, r: PReserved[PSymOp.Or.type])(val pos: (Position, Position)) extends POpApp {
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

  override def prettyNoBrackets = s"|${seq.pretty}|"
}

sealed trait PSetLiteral extends PCollectionLiteral {
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSet(pType)
}

case class PEmptySet(op: PReserved[PKwOp.Set.type], pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], unit: PGrouped[PSym.Paren, Unit])(val pos: (Position, Position)) extends PSetLiteral with PEmptyCollectionLiteral

case class PExplicitSet(op: PReserved[PKwOp.Set.type], args: PSym.Punctuated[PSym.Paren, PExp])(val pos: (Position, Position)) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral {
  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeMultiset(pType)
}

case class PEmptyMultiset(op: PReserved[PKwOp.Multiset.type], pAnnotatedType: Option[PGrouped[PSym.Bracket, PType]], unit: PGrouped[PSym.Paren, Unit])(val pos: (Position, Position)) extends PMultiSetLiteral with PEmptyCollectionLiteral

case class PExplicitMultiset(op: PReserved[PKwOp.Multiset.type], args: PSym.Punctuated[PSym.Paren, PExp])(val pos: (Position, Position)) extends PMultiSetLiteral with PExplicitCollectionLiteral


/* ** Maps */

sealed trait PMapLiteral extends POpApp {
  override val opName = "Map#Map"

  def pKeyType: PType

  def pValueType: PType

  def pMapType(keyType: PType, valueType: PType): PType =
    if (keyType.isUnknown || valueType.isUnknown) PUnknown()()
    else MakeMap(keyType, valueType)
}

case class PEmptyMap(op: PReserved[PKwOp.Map.type], typ: Option[PGrouped[PSym.Bracket, PPairArgument[PType, PType]]], unit: PGrouped[PSym.Paren, Unit])(val pos: (Position, Position)) extends PMapLiteral {
  override val args = Seq()
  override def pKeyType = typ.map(_.inner.first).getOrElse(PTypeVar("#K"))
  override def pValueType = typ.map(_.inner.second).getOrElse(PTypeVar("#E"))

  override val extraLocalTypeVariables: Set[PDomainType] =
    Set(pKeyType, pValueType) collect { case t: PDomainType if t.isTypeVar => t }

  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> pMapType(pKeyType, pValueType)
  ))

  def explicitType: Option[(PType, PType)] = typ.map(t => (t.inner.first, t.inner.second))
  override def prettyNoBrackets =
    s"${op.pretty}${typ.map(_.pretty).getOrElse("")}${unit.pretty(PGrouped.unitToPretty)}"
}

case class PExplicitMap(op: PReserved[PKwOp.Map.type], args: PSym.Punctuated[PSym.Paren, PMaplet])(val pos: (Position, Position)) extends PMapLiteral {
  override def pKeyType: PType = args.head.key.typ

  override def pValueType: PType = args.head.value.typ

  override def signatures: List[PTypeSubstitution] = List(
    args.indices.map {
      case 0 => POpApp.pResS -> POpApp.pArg(0)
      case n => POpApp.pArgS(n) -> POpApp.pArg(0)
    }.toMap
  )

  override def prettyNoBrackets = s"Map(${args.map(_.pretty).mkString(", ")})"
}

/**
  * A key-value pair (i.e., an entry of an `PExplicitMap`) is
  * considered to be a singleton map literal itself.
  */
case class PMaplet(key: PExp, a: PSymOp.Assign, value: PExp)(val pos: (Position, Position)) extends PMapLiteral {
  override def pKeyType: PType = key.typ

  override def pValueType: PType = value.typ

  override def args: Seq[PExp] = Seq(key, value)

  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> MakeMap(POpApp.pArg(0), POpApp.pArg(1))
  ))

  override def prettyNoBrackets = s"${key.pretty} := ${value.pretty}"
}

case class PMapDomain(keyword: PReserved[PKwOp.Domain.type], base: PGrouped[PSym.Paren, PExp])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#domain"
  override val args = Seq(base)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(keyType)
  ))

  override def prettyNoBrackets = s"domain(${base.pretty})"
}

case class PMapRange(keyword: PReserved[PKwOp.Range.type], base: PGrouped[PSym.Paren, PExp])(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#range"
  override val args = Seq(base)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(valueType)
  ))

  override def prettyNoBrackets = s"domain(${base.pretty})"
}


///////////////////////////////////////////////////////////////////////////
// Statements
trait PStmt extends PNode {
  /**
    * Returns a list of all actual statements contained in this statement.  That
    * is, all statements except `Seqn`, including statements in the body of loops, etc.
    */
  // def childStmts: Seq[PStmt] = {
  //   this match {
  //     case PSeqn(ss) => ss
  //     case PIf(_, _, thn, _, els) => Seq(this, thn, els)
  //     case PWhile(_, _, _, body) => Seq(this, body)
  //     case _ => Seq(this)
  //   }
  // }
  // TODO: remove this method
}

case class PAnnotatedStmt(annotation: PAnnotation, stmt: PStmt)(val pos: (Position, Position)) extends PStmt

case class PSeqn(ss: PGrouped[PSym.Brace, PDelimited[PStmt, Option[PSym.Semi]]])(val pos: (Position, Position)) extends PStmt with PScope

/**
  * PSeqn representing the expanded body of a statement macro.
  * Unlike a normal PSeqn, it does not represent its own scope.
  * Is created only temporarily during macro expansion and eliminated (i.e., expanded into the surrounding scope)
  * before translation.
  */
case class PMacroSeqn(ss: Seq[PStmt])(val pos: (Position, Position)) extends PStmt

case class PFold(fold: PReserved[PKw.Fold.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PUnfold(unfold: PReserved[PKw.Unfold.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PPackageWand(pckg: PReserved[PKw.Package.type], wand: PExp, proofScript: Option[PSeqn])(val pos: (Position, Position)) extends PStmt

case class PApplyWand(apply: PReserved[PKw.Apply.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PExhale(exhale: PReserved[PKw.Exhale.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PAssert(assert: PReserved[PKw.Assert.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PAssume(assume: PReserved[PKw.Assume.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

case class PInhale(inhale: PReserved[PKw.Inhale.type], e: PExp)(val pos: (Position, Position)) extends PStmt with PLspStmtWithExp

/** Can also represent a method call or statement macro with no `:=` when `targets` is empty. */
case class PAssign(targets: PDelimited[PAssignTarget, PSym.Comma], op: Option[PReserved[PSymOp.Assign.type]], rhs: PExp)(val pos: (Position, Position)) extends PStmt

sealed trait PIfContinuation extends PNode
case class PIf(keyword: PReserved[PKeywordIf], cond: PExp, thn: PSeqn, els: Option[PIfContinuation])(val pos: (Position, Position)) extends PStmt with PIfContinuation
case class PElse(k: PReserved[PKw.Else.type], els: PSeqn)(val pos: (Position, Position)) extends PNode with PIfContinuation

case class PWhile(keyword: PReserved[PKw.While.type], cond: PExp, invs: PDelimited[PSpecification[PKw.InvSpec], Option[PSym.Semi]], body: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PVars(keyword: PReserved[PKw.Var.type], vars: PDelimited[PLocalVarDecl, PSym.Comma], init: Option[(PReserved[PSymOp.Assign.type], PExp)])(val pos: (Position, Position)) extends PStmt

case class PLabel(label: PReserved[PKw.Label.type], idndef: PIdnDef, invs: PDelimited[PSpecification[PKw.InvSpec], Option[PSym.Semi]])(val pos: (Position, Position)) extends PStmt with PLocalDeclaration {
  override def completionScope: Map[SuggestionScope,Byte] = Map(LabelScope -> 0, StatementScope -> -50)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Event
  override def tokenType = TokenType.Event
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Event
  override def hint = {
    val firstLine = s"${label.pretty} ${idndef.pretty}"
    val invsStr = invs.map(i => s"\n  ${i._1.pretty} ${i._2.pretty}").mkString
    firstLine + invsStr
  }
  override def description: String = "Label"
}

case class PGoto(goto: PReserved[PKw.Goto.type], target: PIdnUseExp)(val pos: (Position, Position)) extends PStmt with HasSemanticHighlights {
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(target).map(sp => SemanticHighlight(sp, TokenType.Event)).toSeq
  // override def getHoverHints: Seq[HoverHint] = target.hoverHint(RangePosition(target))
}

case class PTypeVarDecl(idndef: PIdnDef)(val pos: (Position, Position)) extends PLocalDeclaration {
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.TypeParameter
  override def hint: String = idndef.pretty
  override def completionScope: Map[SuggestionScope,Byte] = Map(TypeScope -> 0)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.TypeParameter
  override def completionChars: Option[Map[Char, Byte]] = Some(Map(':' -> 50))
  override def tokenType = TokenType.TypeParameter
  override def description: String = "Type Variable"
}

case class PSkip()(val pos: (Position, Position)) extends PStmt

case class PQuasihavoc(quasihavoc: PReserved[PKw.Quasihavoc.type], lhs: Option[(PExp, PReserved[PSymOp.Implies.type])], e: PExp)(val pos: (Position, Position)) extends PStmt

case class PQuasihavocall(quasihavocall: PReserved[PKw.Quasihavocall.type], vars: PDelimited[PLogicalVarDecl, PSym.Comma], colons: PReserved[PSym.ColonColon.type], lhs: Option[(PExp, PReserved[PSymOp.Implies.type])], e: PExp)(val pos: (Position, Position)) extends PStmt with PScope

sealed trait PNewArgument

/* new(f1, ..., fn) or new(*) */
case class PNewExp(keyword: PReserved[PKw.New.type], fields: PGrouped[PSym.Paren, Either[PSym.Star, PDelimited[PIdnUseExp, PSym.Comma]]])(val pos: (Position, Position)) extends PExp {
  override def prettyNoBrackets: String = s"${keyword.pretty}${fields.map(_.map(_.pretty)).getOrElse(Seq("*")).mkString("(", ", ", ")")}"
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

// trait PDeclarationSymbol extends PDeclaration with PLspDocumentSymbol {
//   def symbolKind: SymbolKind.SymbolKind
//   def detail: Option[String] = None
//   def isDeprecated: Boolean = false
//   def imports: Option[Path] = None
//   def tags: Seq[SymbolTag.SymbolTag] = if (isDeprecated) Seq(SymbolTag.Deprecated) else Nil

//   override def getSymbol: Option[DocumentSymbol] = (RangePosition(this), RangePosition(idndef)) match {
//     case (Some(range), Some(selectionRange)) => Some(DocumentSymbol(idndef.pretty, detail, range, selectionRange, symbolKind, tags, None, getSymbolChildren))
//     case _ => None
//   }
// }

trait PGlobalCallable extends PGlobalDeclaration with HasFoldingRanges with HasSignatureHelps {
  def keyword: PReserved[_]
  def bodyRange: Option[RangePosition]
  def sig: PSignature[_ <: PAnyFormalArgDecl]
  override def idndef = sig.idndef
  def formalArgs: PDelimited[PAnyFormalArgDecl, PSym.Comma] = sig.formalArgs
  def returnString: Option[String]
  def pres: Seq[(PReserved[_], PExp)]
  def posts: Seq[(PReserved[_], PExp)]
  override def hint: String = {
    val firstLine = s"${keyword.pretty} ${idndef.pretty}(${formalArgs.map(_.pretty).mkString(", ")})${returnString.getOrElse("")}"
    val contract = (pres ++ posts).map(p => s"\n  ${p._1.pretty} ${p._2.pretty}")
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
  def idndef: PIdnDef
  def formalArgs: PDelimited[PAnyFormalArgDecl, PSym.Comma]
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

case class PSignature[+T <: PAnyFormalArgDecl](idndef: PIdnDef, formalArgs: PSym.Punctuated[PSym.Paren, T])(val pos: (Position, Position)) extends PNode

///////////////////////////////////////////////////////////////////////////
// Program Members

case class PProgram(imports: Seq[PImport], macros: Seq[PDefine], domains: Seq[PDomain], fields: Seq[PFields], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod], extensions: Seq[PExtender], errors: Seq[ParseReport])(val pos: (Position, Position)) extends PNode with PProgramLsp

case class PImport(annotations: Seq[PAnnotation], imprt: PReserved[PKw.Import.type], var local: Boolean, file: PStringLiteral)(val pos: (Position, Position)) extends PNode with PLspDocumentSymbol {
  var resolved: Option[Path] = None
  override def getSymbol: Option[DocumentSymbol] = (RangePosition(this), RangePosition(file), resolved) match {
    case (Some(tp), Some(fp), Some(resolved)) =>
      // We avoid any circular dependencies since `resolved` is only set for imports which caused a
      // file to actually be imported.
      Some(DocumentSymbol(resolved.getFileName.toString(), None, tp, fp, SymbolKind.File, Nil, Some(resolved)))
    case _ => None
  }
}

case class PDefine(annotations: Seq[PAnnotation], define: PReserved[PKw.Define.type], idndef: PIdnDef, parameters: Option[PSym.Punctuated[PSym.Paren, PIdnDef]], body: PNode)(val pos: (Position, Position)) extends PSingleMember with PStmt with PAnnotated with PGlobalDeclaration {
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Function
  override def hint: String = {
    val params = parameters.map { case (l, p, r) => p.map(_.pretty).mkString(l.pretty, ", ", r.pretty) }.getOrElse("")
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

case class PDomain(annotations: Seq[PAnnotation], domain: PReserved[PKw.Domain.type], idndef: PIdnDef, typVars: Option[PSym.Punctuated[PSym.Bracket, PTypeVarDecl]], members: PDomainMembers, interpretations: Option[PDomainInterpretations])
                  (val pos: (Position, Position)) extends PSingleMember with PGlobalDeclaration with HasFoldingRanges with HasSuggestionScopeRanges {
  override def tokenType = TokenType.Interface
  override def symbolKind = SymbolKind.Interface
  override def hint = {
    val tvsStr = if (typVars.isEmpty) "" else typVars.map(_.idndef.pretty).mkString("[", ",", "]")
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

case class PDomainFunction(annotations: Seq[PAnnotation], unique: Option[PReserved[PKw.Unique.type]], function: PReserved[PKw.Function.type], sig: PSignature[PAnyFormalArgDecl], c: PSym.Colon, resultType: PType, interpretation: Option[(PReserved[PKw.Interpretation.type], PStringLiteral)], s: Option[PSym.Semi])
                          (val domainName: PIdnRef)(val pos: (Position, Position)) extends PAnyFunction {

  override def keyword = function
  override def pres = Nil
  override def posts = Nil
  override def bodyRange: Option[RangePosition] = None
  override def description: String = "Domain Function"
}
case class PAxiom(annotations: Seq[PAnnotation], axiom: PReserved[PKw.Axiom.type], idndef: Option[PIdnDef], exp: PGrouped[PSym.Brace, PExp], s: Option[PSym.Semi])(val domainName: PIdnRef)(val pos: (Position, Position)) extends PScope with HasFoldingRanges {

  override def getFoldingRanges: Seq[FoldingRange] = RangePosition(exp).map(FoldingRange(_)).toSeq
}
case class PDomainMembers(funcs: Seq[PDomainFunction], axioms: Seq[PAxiom])(val pos: (Position, Position)) extends PNode

case class PDomainInterpretation(name: String, c: PSym.Colon, str: PStringLiteral)(val pos: (Position, Position)) extends PNode
case class PDomainInterpretations(k: PReserved[PKeywordLang], m: PSym.Punctuated[PSym.Paren, PDomainInterpretation])(val pos: (Position, Position)) extends PNode {
  def interps: Map[String, String] = m.inner.toSeq.map(i => i.name -> i.str.grouped.inner).toMap
}

trait PDomainMember1 extends PNode
case class PDomainFunction1(annotations: Seq[PAnnotation], unique: Option[PReserved[PKw.Unique.type]], function: PReserved[PKw.Function.type], sig: PSignature[PAnyFormalArgDecl], c: PSym.Colon, typ: PType, interpretation: Option[(PReserved[PKw.Interpretation.type], PStringLiteral)], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PDomainMember1
case class PAxiom1(annotations: Seq[PAnnotation], axiom: PReserved[PKw.Axiom.type], idndef: Option[PIdnDef], exp: PGrouped[PSym.Brace, PExp], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PDomainMember1
case class PDomainMembers1(members: Seq[PDomainMember1])(val pos: (Position, Position)) extends PNode


case class PFields(annotations: Seq[PAnnotation], field: PReserved[PKw.Field.type], fields: PDelimited[PFieldDecl, PSym.Comma], s: Option[PSym.Semi])(val pos: (Position, Position)) extends PMember {
  override def declares: Seq[PGlobalDeclaration] = fields.toSeq
}

case class PSpecification[+T <: PKw.Spec](k: PReserved[PKw.Spec], e: PExp)(val pos: (Position, Position)) extends PNode

case class PFunction(annotations: Seq[PAnnotation], function: PReserved[PKw.Function.type], sig: PSignature[PFormalArgDecl], c: PSym.Colon, resultType: PType, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]], posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]], body: Option[PGrouped[PSym.Brace, PExp]])
                    (val pos: (Position, Position)) extends PAnyFunction {
  def deepCopy(annotations: Seq[PAnnotation] = this.annotations, function: PReserved[PKw.Function.type] = this.function, sig: PSignature[PFormalArgDecl] = this.sig, c: PSym.Colon = this.c, resultType: PType = this.resultType, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]] = this.pres, posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]] = this.posts, body: Option[PGrouped[PSym.Brace, PExp]] = this.body): PFunction = {
    StrategyBuilder.Slim[PNode]({
      case p: PFunction => PFunction(annotations, function, sig, c, resultType, pres, posts, body)(p.pos)
    }).execute[PFunction](this)
  }

  override def keyword = function
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
  override def description: String = "Function"
}

case class PPredicate(annotations: Seq[PAnnotation], predicate: PReserved[PKw.Predicate.type], sig: PSignature[PFormalArgDecl], body: Option[PGrouped[PSym.Brace, PExp]])(val pos: (Position, Position))
  extends PAnyFunction {

  override def resultType = Bool

  override def returnString: Option[String] = None

  override def tokenType = TokenType.Struct
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Struct
  override def keyword = predicate
  override def pres = Nil
  override def posts = Nil
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Struct
  override def description: String = "Predicate"
}

case class PMethod(annotations: Seq[PAnnotation], method: PReserved[PKw.Method.type], sig: PSignature[PFormalArgDecl], returns: Option[PMethodReturns], pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]], posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]], body: Option[PStmt])
                  (val pos: (Position, Position)) extends PSingleMember with PGlobalDeclaration with PGlobalCallable with HasSuggestionScopeRanges {
  def deepCopy(annotations: Seq[PAnnotation] = this.annotations, method: PReserved[PKw.Method.type] = this.method, sig: PSignature[PFormalArgDecl] = this.sig, returns: Option[PMethodReturns] = this.returns, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]] = this.pres, posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]] = this.posts, body: Option[PStmt] = this.body): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(annotations, method, sig, returns, pres, posts, body)(p.pos)
    }).execute[PMethod](this)
  }

  def deepCopyWithNameSubstitution(annotations: Seq[PAnnotation] = this.annotations, method: PReserved[PKw.Method.type] = this.method, sig: PSignature[PFormalArgDecl] = this.sig, returns: Option[PMethodReturns] = this.returns, pres: PDelimited[PSpecification[PKw.PreSpec], Option[PSym.Semi]] = this.pres, posts: PDelimited[PSpecification[PKw.PostSpec], Option[PSym.Semi]] = this.posts, body: Option[PStmt] = this.body)
                                  (idn_generic_name: String, idn_substitution: String): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(annotations, method, sig, returns, pres, posts, body)(p.pos)
      case p@PIdnDef(name) if name == idn_generic_name => PIdnDef(idn_substitution)(p.pos)
      case p@PIdnUseExp(name) if name == idn_generic_name => PIdnUseExp(idn_substitution)(p.pos)
      case p@PIdnRef(name) if name == idn_generic_name => PIdnRef(idn_substitution)(p.pos)
    }).execute[PMethod](this)
  }

  override def keyword = method
  override def tokenType = TokenType.Method
  override def symbolKind = SymbolKind.Method
  override def returnString: Option[String] = Some(s" returns (${returns.toSeq.flatMap(_.formalReturns.map(_.hint)).mkString(", ")})")
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
  override def getSuggestionScopeRanges: Seq[SuggestionScopeRange] =
    RangePosition(this).map(SuggestionScopeRange(_, CallableSignatureScope)).toSeq ++
    bodyRange.map(SuggestionScopeRange(_, StatementScope)).toSeq
  override def completionScope: Map[SuggestionScope,Byte] = Map(StatementScope -> 0, ExpressionScope -> -20)
  override def completionKind: CompletionKind.CompletionKind = CompletionKind.Method
  override def typeHint: Option[String] = {
    val args = formalArgs.map(_.typ.pretty).mkString("(", ", ", ")")
    val rets = returns.toSeq.flatMap(_.formalReturns.map(_.typ.pretty)).mkString("(", ", ", ")")
    Some(s"$args returns $rets")
  }
  override def description: String = "Method"
}

case class PMethodReturns(k: PReserved[PKw.Returns.type], formalReturns: PGrouped[PSym.Paren, PDelimited[PFormalReturnDecl, PSym.Comma]])(val pos: (Position, Position)) extends PNode

/**
  * Used for parsing annotation for top level members. Passed as an argument to the members to construct them.
  */
case class PAnnotationsPosition(annotations: Seq[PAnnotation], pos: (Position, Position))
case class PAnnotation(at: PReserved[PSym.At.type], key: PIdnRef, values: PGrouped[PSym.Paren, PDelimited[PStringLiteral, PSym.Comma]])(val pos: (Position, Position)) extends PNode with PAnnotationLsp

case class PStringLiteral(grouped: PGrouped[_, String])(val pos: (Position, Position)) extends PNode with PLeaf with PStringLiteralLsp

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
  def getSubnodes(): Seq[PNode] = ???

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


// /**
//   * Utility methods for parser parserAST nodes.
//   */
// object Nodes {
//   def node(n: Any): Option[PNode] = if (n.isInstanceOf[PNode]) Some(n.asInstanceOf[PNode]) else None

//   // /**
//   //   * See PNode.subnodes.
//   //   */
//   // def subnodes(n: PNode): Seq[PNode] = {
//   //   n match {
//   //     case PReserved(_) => Nil
//   //     case PIdnDef(_) => Nil
//   //     case PIdnUseExp(_) => Nil
//   //     case PIdnRef(_) => Nil
//   //     case PUnnamedFormalArgDecl(typ) => Seq(typ)
//   //     case PFormalArgDecl(idndef, typ) => Seq(idndef, typ)
//   //     case PFormalReturnDecl(idndef, typ) => Seq(idndef, typ)
//   //     case PLogicalVarDecl(idndef, typ) => Seq(idndef, typ)
//   //     case PLocalVarDecl(idndef, typ) => Seq(idndef, typ)
//   //     case PFieldDecl(idndef, typ) => Seq(idndef, typ)
//   //     case PPrimitiv(keyword) => Seq(keyword)
//   //     case PDomainType(domain, args) => Seq(domain) ++ args.toSeq.flatMap(a => Seq(a._1) ++ a._2 ++ Seq(a._3))
//   //     case PSeqType(seq, elemType) => Seq(seq, elemType)
//   //     case PSetType(set, elemType) => Seq(set, elemType)
//   //     case PMultisetType(multiset, elemType) => Seq(multiset, elemType)
//   //     case PMapType(map, keyType, valueType) => Seq(map, keyType, valueType)
//   //     case PUnknown() => Nil
//   //     case PBinExp(left, op, right) => Seq(left, op, right)
//   //     case PMagicWandExp(left, wand, right) => Seq(left, wand, right)
//   //     case PUnExp(op, exp) => Seq(op, exp)
//   //     case PTrigger(l, exp, r) => Seq(l) ++ exp ++ Seq(r)
//   //     case PIntLit(_) => Nil
//   //     case PBoolLit(keyword, _) => Seq(keyword)
//   //     case PNullLit(nul) => Seq(nul)
//   //     case PWandType() => Nil
//   //     case PFunctionType(args, result) => args ++ Seq(result)
//   //     case PResultLit(result) => Seq(result)
//   //     case PFieldAccess(rcv, dot, field) => Seq(rcv, dot, field)
//   //     case PCall(func, l, args, r, optType) => Seq(func, l) ++ args ++ Seq(r) ++ optType.toSeq.flatMap(o => Seq(o._1, o._2))
//   //     case PUnfolding(unfolding, acc, in, exp) => Seq(unfolding, acc, in, exp)
//   //     case PApplying(applying, wand, in, exp) => Seq(applying, wand, in, exp)
//   //     case PExists(exists, vars, cs, triggers, exp) => Seq(exists) ++ vars ++ Seq(cs) ++ triggers ++ Seq(exp)
//   //     case POldExp(k, id, l, e, r) => Seq(k) ++ id.toSeq.flatMap(i => Seq(i._1, i._2, i._3)) ++ Seq(l, e, r)
//   //     case PLet(op, variable, eq, exp, in, nestedScope) => Seq(op, variable, eq, exp, in, nestedScope)
//   //     case PLetNestedScope(body) => Seq(body)
//   //     case PForall(forall, vars, cs, triggers, exp) => Seq(forall) ++ vars ++ Seq(cs) ++ triggers ++ Seq(exp)
//   //     case PForPerm(forperm, vars, res, cs, expr) => Seq(forperm) ++ vars ++ Seq(res, cs, expr)
//   //     case PCondExp(cond, q, thn, c, els) => Seq(cond, q, thn, c, els)
//   //     case PInhaleExhaleExp(l, in, c, ex, r) => Seq(l, in, c, ex, r)
//   //     case PCurPerm(k, l, loc, r) => Seq(k, l, loc, r)
//   //     case PNoPerm(k) => Seq(k)
//   //     case PFullPerm(k) => Seq(k)
//   //     case PWildcard(k) => Seq(k)
//   //     case PEpsilon(k) => Seq(k)
//   //     case PAccPred(acc, l, loc, perm, r) => Seq(acc, l, loc, perm, r)
//   //     case PEmptySeq(k, t, l, r) => Seq(k, t, l, r)
//   //     case PExplicitSeq(k, l, elems, r) => Seq(k, l) ++ elems ++ Seq(r)
//   //     case PRangeSeq(l, low, ds, high, r) => Seq(l, low, ds, high, r)
//   //     case PSeqSlice(seq, l, s, d, e, r) => Seq(seq, l) ++ s.toSeq ++ Seq(d) ++ e.toSeq ++ Seq(r)
//   //     case PLookup(seq, l, idx, r) => Seq(seq, l, idx, r)
//   //     case PUpdate(seq, l, idx, a, elem, r) => Seq(seq, l, idx, a, elem, r)
//   //     case PSize(seq) => Seq(seq)
//   //     case PEmptySet(k, t, l, r) => Seq(k, t, l, r)
//   //     case PExplicitSet(k, l, elems, r) => Seq(k, l) ++ elems ++ Seq(r)
//   //     case PEmptyMultiset(k, t, l, r) => Seq(k, t, l, r)
//   //     case PExplicitMultiset(k, l, elems, r) => Seq(k, l) ++ elems ++ Seq(r)
//   //     case PEmptyMap(kw, k, v, l, r) => Seq(kw, k, v, l, r)
//   //     case PExplicitMap(k, l, elems, r) => Seq(k, l) ++ elems ++ Seq(r)
//   //     case PMapRange(op, l, base, r) => Seq(op, l, base, r)
//   //     case PMapDomain(op, l, base, r) => Seq(op, l, base, r)
//   //     case PMaplet(key, a, value) => Seq(key, a, value)
//   //     case PSeqn(l, ss, r) => Seq(l) ++ ss ++ Seq(r)
//   //     case PFold(fold, exp) => Seq(fold, exp)
//   //     case PUnfold(unfold, exp) => Seq(unfold, exp)
//   //     case PPackageWand(pckg, exp, proofScript) => Seq(pckg, exp) ++ proofScript.toSeq
//   //     case PApplyWand(apply, exp) => Seq(apply, exp)
//   //     case PExhale(exhale, exp) => Seq(exhale, exp)
//   //     case PAssert(assert, exp) => Seq(assert, exp)
//   //     case PInhale(inhale, exp) => Seq(inhale, exp)
//   //     case PAssume(assume, exp) => Seq(assume, exp)
//   //     case PNewExp(k, l, fields, r) => Seq(k, l) ++ fields.getOrElse(Nil) ++ Seq(r)
//   //     case PLabel(label, name, invs) => Seq(label, name) ++ invs.flatMap(inv => Seq(inv._1, inv._2))
//   //     case PGoto(goto, label) => Seq(goto, label)
//   //     case PAssign(targets, op, rhs) => targets ++ op.toSeq ++ Seq(rhs)
//   //     case PIf(keyword, cond, thn, els) => Seq(keyword, cond, thn) ++ els.map(_.merge).toSeq
//   //     case PElse(k, els) => Seq(k, els)
//   //     case PWhile(keyword, cond, invs, body) => Seq(keyword, cond) ++ invs.flatMap(inv => Seq(inv._1, inv._2)) ++ Seq(body)
//   //     case PVars(k, vars, init) => Seq(k) ++ vars ++ init.toSeq.flatMap(i => Seq(i._1, i._2))
//   //     case PProgram(imports, macros, domains, fields, functions, predicates, methods, extensions, _) =>
//   //       imports ++ macros ++ domains ++ fields ++ functions ++ predicates ++ methods ++ extensions
//   //     case PStringLiteral(l, _, r) => Seq(l, r)
//   //     case PImport(anns, imprt, _, file) => anns ++ Seq(imprt, file)
//   //     case PDomain(anns, domain, idndef, typVars, members, i) => anns ++ Seq(domain, idndef) ++ typVars ++ Seq(members) ++ i.toSeq
//   //     case PDomainMembers(funcs, axioms) => funcs ++ axioms
//   //     case PDomainInterpretations(k, l, m, r) => Seq(k, l) ++ m.flatMap(c => Seq(c._2, c._3)) ++ Seq(r)
//   //     case PFields(anns, field, fields) => anns ++ Seq(field) ++ fields
//   //     case PSignature(idndef, l, formalArgs, r) => Seq(idndef, l) ++ formalArgs ++ Seq(r)
//   //     case PMethod(anns, method, sig, returns, pres, posts, body) =>
//   //       anns ++ Seq(method, sig) ++ returns.toSeq ++ pres.flatMap(c => Seq(c._1, c._2)) ++ posts.flatMap(c => Seq(c._1, c._2)) ++ body.toSeq
//   //     case PMethodReturns(k, l, formalReturns, r) => Seq(k, l) ++ formalReturns ++ Seq(r)
//   //     case PFunction(anns, function, sig, c, typ, pres, posts, body) =>
//   //       anns ++ Seq(function, sig, c, typ) ++ pres.flatMap(c => Seq(c._1, c._2)) ++ posts.flatMap(c => Seq(c._1, c._2)) ++ body
//   //     case PDomainFunction(anns, unique, function, sig, c, typ, i) =>
//   //       anns ++ unique.toSeq ++ Seq(function, sig, c, typ) ++ i.toSeq.flatMap(i => Seq(i._1, i._2))
//   //     case PPredicate(anns, predicate, sig, body) =>
//   //       anns ++ Seq(predicate, sig) ++ body
//   //     case PAxiom(anns, axiom, idndef, exp) => anns ++ Seq(axiom) ++ idndef.toSeq ++ Seq(exp)
//   //     case PTypeVarDecl(name) => Seq(name)
//   //     case PDefine(anns, define, idndef, optArgs, body) =>
//   //       anns ++ Seq(define, idndef) ++ optArgs.toSeq.flatMap { case (l, o, r) => Seq(l) ++ o ++ Seq(r) } ++ Seq(body)
//   //     case PQuasihavoc(quasihavoc, lhs, e) =>
//   //       Seq(quasihavoc) ++ lhs.toSeq.flatMap(lhs => Seq(lhs._1, lhs._2)) ++ Seq(e)
//   //     case PQuasihavocall(quasihavocall, vars, cc, lhs, e) =>
//   //       Seq(quasihavocall) ++ vars ++ Seq(cc) ++ lhs.toSeq.flatMap(lhs => Seq(lhs._1, lhs._2)) ++ Seq(e)
//   //     case PAnnotatedExp(ann, e) => Seq(ann, e)
//   //     case PAnnotatedStmt(ann, s) => Seq(ann, s)
//   //     case PGrouped(l, g: PNode, r) => Seq(l, g, r)
//   //     case PGrouped(l, _, r) => Seq(l, r)
//   //     case PDelimited(first, inner, end) => first.toSeq ++ inner.flatMap(i => Seq(i._1, i._2)) ++ end.toSeq
//   //     case PAnnotation(at, key, l, values, r) => Seq(at, key, l) ++ values ++ Seq(r)
//   //     case t: PExtender => t.getSubnodes()
//   //     case _: PSkip => Nil
//   //   }
//   // }
// }
