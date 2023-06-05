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

trait Where {
  val pos: (Position, Position)
}

/**
  * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
  * with the actual Viper abstract syntax tree.
  */
trait PNode extends Where with Product with Rewritable {

  /** Returns a list of all direct sub-nodes of this node. */
  def subnodes = Nodes.subnodes(this)

  /** @see [[Visitor.reduceTree()]] */
  def reduceTree[T](f: (PNode, Seq[T]) => T) = Visitor.reduceTree(this, Nodes.subnodes)(f)

  /** @see [[Visitor.reduceWithContext()]] */
  def reduceWithContext[C, R](context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R) = {
    Visitor.reduceWithContext(this, Nodes.subnodes)(context, enter, combine)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f: PartialFunction[PNode, Unit]): Unit = {
    Visitor.visit(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f1: PartialFunction[PNode, Unit], f2: PartialFunction[PNode, Unit]): Unit = {
    Visitor.visit(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f: PNode => Boolean): Unit = {
    Visitor.visitOpt(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f1: PNode => Boolean, f2: PNode => Unit): Unit = {
    Visitor.visitOpt(this, Nodes.subnodes, f1, f2)
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
    Visitor.deepCollect(Seq(this), Nodes.subnodes)(f)

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[PNode, R]): Seq[R] =
    Visitor.shallowCollect(Seq(this), Nodes.subnodes)(f)

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
        case Some(o) =>
          setNodeChildConnections(o)
        case s: Iterable[_] =>
          for (v <- s)
            setNodeChildConnections(v)
        case _ =>
        // Ignore other kinds of nodes
      }

    _children.clear()
    for (c <- productIterator)
      setNodeChildConnections(c)

  }
}

object TypeHelper {
  val Int = PPrimitiv("Int")((NoPosition, NoPosition))
  val Bool = PPrimitiv("Bool")((NoPosition, NoPosition))
  val Perm = PPrimitiv("Perm")((NoPosition, NoPosition))
  val Ref = PPrimitiv("Ref")((NoPosition, NoPosition))
  val Pred = PPredicateType()((NoPosition, NoPosition))
  val Wand = PWandType()((NoPosition, NoPosition))
}

// Identifiers (uses and definitions)
trait PIdentifier {
  def name: String
}

case class PIdnDef(name: String)(val pos: (Position, Position)) extends PNode with PIdentifier

case class PIdnUse(name: String)(val pos: (Position, Position)) extends PExp with PIdentifier with PAssignTarget with PMaybeMacroExp {
  var decl: PTypedDeclaration = null
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
}

trait PAnyFormalArgDecl extends PNode with PUnnamedTypedDeclaration

case class PUnnamedFormalArgDecl(var typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl

/** Any `var: Type` style binding, only useful during parsing and therefore not a `PNode`. */
case class PIdnTypeBinding(idndef: PIdnDef, typ: PType)(val pos: (Position, Position))

/** Anything that can be `PIdnUse`d as an expression (e.g. the receiver of a `PFieldAccess`). */
trait PAnyVarDecl extends PTypedDeclaration
/** Anything that can be `PIdnUse`d as the target of a `PAssign`. */
trait PAssignableVarDecl extends PAnyVarDecl

/** Any argument to a method, function or predicate. */
case class PFormalArgDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl with PAnyVarDecl with PLocalDeclaration
object PFormalArgDecl {
  def apply(d: PIdnTypeBinding): PFormalArgDecl = PFormalArgDecl(d.idndef, d.typ)(d.pos)
}
/** The return arguments of methods. */
case class PFormalReturnDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PAssignableVarDecl with PLocalDeclaration
object PFormalReturnDecl {
  def apply(d: PIdnTypeBinding): PFormalReturnDecl = PFormalReturnDecl(d.idndef, d.typ)(d.pos)
}
/** Any immutable variable binding, e.g. under quantifiers, let expressions.
 * [2014-11-13 Malte] Changed type to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PLogicalVarDecl(idndef: PIdnDef, var typ: PType)(val pos: (Position, Position)) extends PAnyVarDecl with PLocalDeclaration
object PLogicalVarDecl {
  def apply(d: PIdnTypeBinding): PLogicalVarDecl = PLogicalVarDecl(d.idndef, d.typ)(d.pos)
}
/** Declaration of a local variable. */
case class PLocalVarDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PAssignableVarDecl with PLocalDeclaration {
  def toIdnUse: PIdnUse = {
    val use = PIdnUse(idndef.name)(idndef.pos)
    use.typ = typ
    use.decl = this
    use
  }
}
object PLocalVarDecl {
  def apply(d: PIdnTypeBinding): PLocalVarDecl = PLocalVarDecl(d.idndef, d.typ)(d.pos)
}
case class PFieldDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PTypedDeclaration with PGlobalDeclaration
object PFieldDecl {
  def apply(d: PIdnTypeBinding): PFieldDecl = PFieldDecl(d.idndef, d.typ)(d.pos)
}

// Types
trait PType extends PNode {
  def isUnknown: Boolean = this.isInstanceOf[PUnknown]

  def isValidOrUndeclared: Boolean

  def isGround: Boolean = true

  //  def substitute(newTypVarsMap: Map[String, PType]): PType = this
  def substitute(ts: PTypeSubstitution): PType

  def subNodes: Seq[PType]

  //If we add type quantification or any type binders we need to modify this
  def freeTypeVariables: Set[String] =
    subNodes.flatMap(_.freeTypeVariables).toSet union
      (this match {
        case pdt: PDomainType if pdt.isTypeVar && PTypeVar.isFreePTVName(pdt.domain.name) => Set(pdt.genericName)
        case _ => Set()
      })

  //    def isDisjoint[T](s1:Set[T],s2:Set[T]) = (s1 intersect s2).isEmpty
}


case class PPrimitiv(name: String)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType {
  override def substitute(ts: PTypeSubstitution): PType = this

  override val subNodes = Seq()

  override def toString = name

  override def isValidOrUndeclared = true
}

case class PDomainType(domain: PIdnUse, args: Seq[PType])(val pos: (Position, Position)) extends PGenericType {
  val genericName = domain.name
  override val typeArguments = args //if (kind==PDomainTypeKinds.Domain)
  var kind: PDomainTypeKinds.Kind = PDomainTypeKinds.Unresolved
  override val subNodes = args

  /* This class is also used to represent type variables, as they cannot
   * be distinguished syntactically from domain types without generic arguments.
   * For type variables, we have args.length = 0
   */
  def isTypeVar = kind == PDomainTypeKinds.TypeVar

  override def isValidOrUndeclared =
    (isTypeVar || kind == PDomainTypeKinds.Domain || kind == PDomainTypeKinds.Undeclared) &&
      args.forall(_.isValidOrUndeclared)


  def isResolved = kind != PDomainTypeKinds.Unresolved

  def isUndeclared = kind == PDomainTypeKinds.Undeclared

  override def isGround: Boolean = {
    args.forall(_.isGround) && (!isTypeVar || !PTypeVar.isFreePTVName(domain.name))
  }

  override def substitute(ts: PTypeSubstitution): PType = {
    require(kind == PDomainTypeKinds.Domain || kind == PDomainTypeKinds.TypeVar || kind == PDomainTypeKinds.Undeclared)
    if (isTypeVar)
      if (ts.isDefinedAt(domain.name))
        return ts.get(domain.name).get
      else
        return this

    val newArgs = args map (a => a.substitute(ts))
    if (args == newArgs)
      return this

    val r = PDomainType(domain, newArgs)((NoPosition, NoPosition))
    r.kind = PDomainTypeKinds.Domain
    r
  }

  override def withTypeArguments(s: Seq[PType]) = copy(args = s)(pos)

  override def toString = domain.name + (if (args.isEmpty) "" else s"[${args.mkString(", ")}]")
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
    val t = PDomainType(PIdnUse(name)((NoPosition, NoPosition)), Nil)((NoPosition, NoPosition))
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

  override def toString = s"$genericName[${typeArguments.mkString(", ")}]"

  def withTypeArguments(s: Seq[PType]): PGenericType
}

sealed trait PGenericCollectionType extends PGenericType {
  def elementType: PType

  override val typeArguments = Seq(elementType)
  override val subNodes = Seq(elementType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)
}

case class PSeqType(elementType: PType)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType with PGenericCollectionType {
  override val genericName = "Seq"

  override def substitute(map: PTypeSubstitution) = PSeqType(elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PSetType(elementType: PType)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType with PGenericCollectionType {
  override val genericName = "Set"

  override def substitute(map: PTypeSubstitution) = PSetType(elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PMultisetType(elementType: PType)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"

  override def substitute(map: PTypeSubstitution) = PMultisetType(elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMultisetType = copy(elementType = s.head)(pos)
}

case class PMapType(keyType: PType, valueType: PType)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType with PGenericType {
  override val genericName = "Map"
  override val subNodes = Seq(keyType, valueType)
  override val typeArguments = Seq(keyType, valueType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)

  override def substitute(map: PTypeSubstitution) = PMapType(keyType.substitute(map), valueType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMapType = copy(keyType = s.head, valueType = s(1))(pos)
}

/** Exists temporarily after parsing and is replaced with
 * a real type by macro expansion.
 */
case class PMacroType(use: PCall) extends PType {
  override val pos: (Position, Position) = use.pos
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
  override def toString = "<error type>"

  override def isValidOrUndeclared = false
}

// used during resolving for predicate accesses
case class PPredicateType()(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PInternalType {
  override def toString = "$predicate"

  override def isValidOrUndeclared = true
}

case class PWandType()(val pos: (Position, Position)) extends PInternalType {
  override def toString = "$wand"

  override def isValidOrUndeclared = true
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
  override def toString = argTypes.mkString("(", ",", ")") + ":" + resultType.toString
}

///////////////////////////////////////////////////////////////////////////////////////
// Expressions
// typeSubstitutions are the possible substitutions used for type checking and inference
// The argument types are unified with the (fresh versions of) types  are
trait PExp extends PNode {
  var typ: PType = PUnknown()()

  def typeSubstitutions: scala.collection.Seq[PTypeSubstitution]

  def forceSubstitution(ts: PTypeSubstitution): Unit
}

case class PAnnotatedExp(e: PExp, annotation: (String, Seq[String]))(val pos: (Position, Position)) extends PExp {
  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = e.typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = e.forceSubstitution(ts)
}

case class PMagicWandExp(override val left: PExp, override val right: PExp)(val posi: (Position, Position)) extends PBinExp(left, MagicWandOp.op, right)(posi) with PResourceAccess

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

case class PCall(func: PIdnUse, args: Seq[PExp], typeAnnotated: Option[PType] = None)(val pos: (Position, Position)) extends POpApp with PLocationAccess with PAssignTarget with PMaybeMacroExp {
  override val idnuse = func
  override val opName = func.name
  override def possibleMacro = if (typeAnnotated.isEmpty) Some(idnuse) else None
  override def macroArgs = args

  override def signatures = if (function != null && function.formalArgs.size == args.size) (function match {
    case pf: PFunction => List(
      new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> pf.formalArgs(i).typ) :+ (POpApp.pRes.domain.name -> pf.typ.resultType))
    )
    case pdf: PDomainFunction =>
      List(
        new PTypeSubstitution(
          args.indices.map(i => POpApp.pArg(i).domain.name -> pdf.formalArgs(i).typ.substitute(domainTypeRenaming.get)) :+
            (POpApp.pRes.domain.name -> pdf.typ.resultType.substitute(domainTypeRenaming.get)))
      )

  })
  else if (extfunction != null && extfunction.formalArgs.size == args.size) (extfunction match {
    case _: PPredicate => List(
      new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> extfunction.formalArgs(i).typ) :+ (POpApp.pRes.domain.name -> Bool))
    )
  })


  else List() // this case is handled in Resolver.scala (- method check) which generates the appropriate error message

  var function: PAnyFunction = null
  var extfunction: PPredicate = null

  override def extraLocalTypeVariables = _extraLocalTypeVariables

  var _extraLocalTypeVariables: Set[PDomainType] = Set()
  var domainTypeRenaming: Option[PTypeRenaming] = None

  def isDomainFunction = domainTypeRenaming.isDefined

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

case class PTrigger(exp: Seq[PExp])(val pos: (Position, Position)) extends PNode

class PBinExp(val left: PExp, val opName: String, val right: PExp)(val pos: (Position, Position)) extends POpApp {

  override val args = Seq(left, right)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    opName match {
      case "++" | "union" | "intersection" | "setminus" | "subset" | "in" => Set(extraElementType)
      case _ => Set()
    }
  val signatures: List[PTypeSubstitution] = opName match {
    case "+" | "-" => List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int)
    )
    case "*" => List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int)
    )
    case "/" => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Int, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Perm),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int)
    )
    case "\\" | "%" => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Int))
    case "<" | "<=" | ">" | ">=" => List(
      Map(POpApp.pArgS(0) -> Perm, POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> Bool)
    )
    case "==" | "!=" => List(
      Map(POpApp.pArgS(1) -> POpApp.pArg(0), POpApp.pResS -> Bool))
    case "&&" | "||" | "<==>" | "==>" => List(
      Map(POpApp.pArgS(1) -> Bool, POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool))
    case MagicWandOp.op => List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Wand),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Wand, POpApp.pResS -> Wand),
      Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Wand, POpApp.pResS -> Bool))
    case "in" => List(
      /* Maps
      Map(POpApp.pArgS(1) -> PSetType(POpApp.pArg(0))(), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> PSeqType(POpApp.pArg(0))(), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> PMultisetType(POpApp.pArg(0))(), POpApp.pResS -> Int)
       */
      Map(POpApp.pArgS(1) -> PSetType(POpApp.pArg(0))(), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> PSeqType(POpApp.pArg(0))(), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> PMultisetType(POpApp.pArg(0))(), POpApp.pResS -> Int),
      Map(POpApp.pArgS(1) -> PMapType(POpApp.pArg(0), extraElementType)(), POpApp.pResS -> Bool)
    )
    case "++" => List(
      Map(POpApp.pArgS(0) -> PSeqType(extraElementType)(), POpApp.pArgS(1) -> PSeqType(extraElementType)(), POpApp.pResS -> PSeqType(extraElementType)())
    )
    case "union" | "intersection" | "setminus" => List(
      Map(POpApp.pArgS(0) -> PSetType(extraElementType)(), POpApp.pArgS(1) -> PSetType(extraElementType)(), POpApp.pResS -> PSetType(extraElementType)()),
      Map(POpApp.pArgS(0) -> PMultisetType(extraElementType)(), POpApp.pArgS(1) -> PMultisetType(extraElementType)(), POpApp.pResS -> PMultisetType(extraElementType)())
    )
    case "subset" => List(
      Map(POpApp.pArgS(0) -> PSetType(extraElementType)(), POpApp.pArgS(1) -> PSetType(extraElementType)(), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> PMultisetType(extraElementType)(), POpApp.pArgS(1) -> PMultisetType(extraElementType)(), POpApp.pResS -> Bool)
    )
    case _ => sys.error(s"internal error - unknown binary operator $opName")
  }

  override def canEqual(that: Any): Boolean = that.isInstanceOf[PBinExp]

  override def productElement(n: Int): Any = n match {
    case 0 => left
    case 1 => opName
    case 2 => right
    case _ => throw new IndexOutOfBoundsException
  }

  override def productArity: Int = 3

  override def equals(that: Any): Boolean = {
    if (this.canEqual(that)) {
      val other = that.asInstanceOf[PBinExp]
      other.opName.equals(this.opName) && other.right.equals(this.right) && other.left.equals(this.left)
    } else false
  }

  override def hashCode(): Int = viper.silver.utility.Common.generateHashCode(left, opName, right)
}

object PBinExp {

  def apply(left: PExp, opName: String, right: PExp)(pos: (Position, Position)): PBinExp =
    new PBinExp(left, opName, right)(pos)

  def unapply(arg: PBinExp): Option[(PExp, String, PExp)] = Some(arg.left, arg.opName, arg.right)
}

case class PUnExp(opName: String, exp: PExp)(val pos: (Position, Position)) extends POpApp {
  override val args = Seq(exp)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    opName match {
      case "++" | "union" | "intersection" | "setminus" | "subset" | "in" => Set(extraElementType)
      case _ => Set()
    }
  override val signatures: List[PTypeSubstitution] = opName match {
    case "-" => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pResS -> Int),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pResS -> Perm)
    )
    case "!" => List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool)
    )
    case _ => sys.error(s"internal error - unknown unary operator $opName")
  }
}

case class PCondExp(cond: PExp, thn: PExp, els: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "?:"
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

case class PIntLit(i: BigInt)(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Int
}

case class PResultLit()(val pos: (Position, Position)) extends PSimpleLiteral

case class PBoolLit(b: Boolean)(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Bool
}

case class PNullLit()(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Ref
}

//sealed trait PHeapOpApp extends POpApp{final override val extraLocalTypeVariables = Set()}
sealed trait PHeapOpApp extends POpApp {
  //  val _typeSubstitutions : Set[PTypeSubstitution] = Set(PTypeSubstitution.id)
  //  override final val typeSubstitutions = _typeSubstitutions
}

sealed trait PResourceAccess extends PHeapOpApp

trait PLocationAccess extends PResourceAccess {
  def idnuse: PIdnUse
}

case class PFieldAccess(rcv: PExp, idnuse: PIdnUse)(val pos: (Position, Position)) extends PLocationAccess with PAssignTarget {
  override final val opName = "."
  override final val args = Seq(rcv)

  override def signatures =
    if (Set(rcv.typ, idnuse.typ).forall(_.isValidOrUndeclared))
      List(PTypeSubstitution(Map(POpApp.pArgS(0) -> Ref, POpApp.pResS -> idnuse.typ)))
    else
      List()
  //setType()
}

case class PUnfolding(acc: PAccPred, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override final val opName = "unfolding"
  override val args = Seq(acc, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)))

  //  check(e.acc.perm, Perm)
  //  check(e.acc.loc, Pred)
  //  acceptNonAbstractPredicateAccess(e.acc, "abstract predicates cannot be (un)folded")
}

case class PApplying(wand: PExp, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override val opName = "applying"
  override val args = Seq(wand, exp)
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

sealed trait PQuantifier extends PBinder {
  def vars: Seq[PLogicalVarDecl]
  def triggers: Seq[PTrigger]
  override def boundVars = vars
}

case class PExists(vars: Seq[PLogicalVarDecl], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForall(vars: Seq[PLogicalVarDecl], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForPerm(vars: Seq[PLogicalVarDecl], accessRes: PResourceAccess, body: PExp)(val pos: (Position, Position)) extends PQuantifier {
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
case class PLet(exp: PExp, nestedScope: PLetNestedScope)(val pos: (Position, Position)) extends PExp {
  override def typeSubstitutions = (for (ts1 <- nestedScope.body.typeSubstitutions; ts2 <- exp.typeSubstitutions) yield (ts1 * ts2).toOption).flatten.toList.distinct
  override def forceSubstitution(ts: PTypeSubstitution) = {
    exp.forceSubstitution(ts)
    nestedScope.variable.typ = exp.typ
    nestedScope.forceSubstitution(ts)
  }
}

case class PLetNestedScope(variable: PLogicalVarDecl, body: PExp)(val pos: (Position, Position)) extends PNode with PBinder {
  override val boundVars = Seq(variable)
}

case class PInhaleExhaleExp(in: PExp, ex: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override val opName = "#inhale#exhale"
  override val args = Seq(in, ex)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool)
  )
}

case class PCurPerm(res: PResourceAccess)(val pos: (Position, Position)) extends PHeapOpApp {
  override val opName = "#perm"
  override val args = Seq(res)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> Perm)
  )
}

case class PNoPerm()(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Perm
}

case class PFullPerm()(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Perm
}

case class PWildcard()(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Perm
}

case class PEpsilon()(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Perm
}

case class PAccPred(loc: PLocationAccess, perm: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "acc"
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool))
  override val args = Seq(loc, perm)
}

sealed trait POldExp extends PHeapOpApp {
  def e: PExp

  override val args = Seq(e)
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> POpApp.pArg(0)))
}

case class POld(e: PExp)(val pos: (Position, Position)) extends POldExp {
  override val opName = "old"
}

case class PLabelledOld(label: PIdnUse, e: PExp)(val pos: (Position, Position)) extends POldExp {
  override val opName = "old#labeled"
}

sealed trait PCollectionLiteral extends POpApp {
  def pElementType: PType

  def pCollectionType(pType: PType): PType
}

sealed trait PEmptyCollectionLiteral extends PCollectionLiteral {
  override val extraLocalTypeVariables: Set[PDomainType] =
    pElementType match {
      case pdt: PDomainType if pdt.isTypeVar => Set(pdt)
      case _ => Set()
    }

  override def signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pResS -> pCollectionType(pElementType)))

  override val args = Seq()
}

sealed trait PExplicitCollectionLiteral extends PCollectionLiteral {
  override val signatures: List[PTypeSubstitution] =
    List(
      ((0 until args.size) map
        (n => if (n == 0) POpApp.pResS -> pCollectionType(POpApp.pArg(0)) else POpApp.pArgS(n) -> POpApp.pArg(0))).toMap
    )

  override val pElementType = args.head.typ
}

sealed trait PSeqLiteral extends PCollectionLiteral {
  override val opName = "Seq#Seq"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else PSeqType(pType)()
}

case class PEmptySeq(pElementType: PType)(val pos: (Position, Position)) extends PSeqLiteral with PEmptyCollectionLiteral

case class PExplicitSeq(override val args: Seq[PExp])(val pos: (Position, Position)) extends PSeqLiteral with PExplicitCollectionLiteral

case class PRangeSeq(low: PExp, high: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#RangeSeq"
  override val args = Seq(low, high)
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> PSeqType(Int)()))
}

case class PSeqIndex(seq: PExp, idx: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#At"
  override val args = Seq(seq, idx)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> PSeqType(POpApp.pRes)(),
      POpApp.pArgS(1) -> Int)
  )
}

case class PLookup(base: PExp, idx: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)

  override val opName = "lookup"
  override val args = Seq(base, idx)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> PSeqType(POpApp.pRes)(), POpApp.pArgS(1) -> Int),
    Map(POpApp.pArgS(0) -> PMapType(keyType, POpApp.pRes)())
  )
}

// Maps: case class PSeqTake(seq: PExp, n: PExp) extends POpApp{
case class PSeqTake(seq: PExp, n: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#Take"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq, n)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> PSeqType(elementType)(),
      POpApp.pArgS(1) -> Int,
      POpApp.pResS -> PSeqType(elementType)()
    ))
}

case class PSeqDrop(seq: PExp, n: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#Drop"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq, n)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> PSeqType(elementType)(),
      POpApp.pArgS(1) -> Int,
      POpApp.pResS -> PSeqType(elementType)()
    ))
}

case class PSeqUpdate(seq: PExp, idx: PExp, elem: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#update"
  val elementType = POpApp.pArg(2)
  override val args = Seq(seq, idx, elem)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> PSeqType(elementType)(),
      POpApp.pArgS(1) -> Int,
      POpApp.pResS -> PSeqType(elementType)()
    ))
  override val extraLocalTypeVariables = Set(elementType)
}

case class PUpdate(base: PExp, key: PExp, value: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)
  val elementType: PDomainType = POpApp.pArg(2)

  override val opName = "update"
  override val args = Seq(base, key, value)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, elementType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> PSeqType(elementType)(), POpApp.pArgS(1) -> Int, POpApp.pResS -> PSeqType(elementType)()),
    Map(POpApp.pArgS(0) -> PMapType(keyType, elementType)(), POpApp.pResS -> PMapType(keyType, elementType)())
  )
}

/* Maps:
case class PSize(seq: PExp)(val pos: (Position, Position)) extends POpApp{
  override val opName = "Seq#size"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
 */

case class PSize(seq: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val elementType: PDomainType = PTypeVar("#E")

  override val opName = "size"
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, elementType)
  override val args = Seq(seq)

  override val signatures: List[PTypeSubstitution] = List(
    // Maps:
    //Map(POpApp.pArgS(0)->PSeqType(elementType)(),POpApp.pResS->Int),
    //Map(POpApp.pArgS(0)->PSetType(elementType)(),POpApp.pResS->Int),
    //Map(POpApp.pArgS(0)->PMultisetType(elementType)(),POpApp.pResS->Int)
    Map(POpApp.pArgS(0) -> PSeqType(elementType)(), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> PSetType(elementType)(), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> PMultisetType(elementType)(), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> PMapType(keyType, elementType)(), POpApp.pResS -> Int)
  )
}

sealed trait PSetLiteral extends PCollectionLiteral {
  override val opName = "Set#Set"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else PSetType(pType)()
}

case class PEmptySet(pElementType: PType)(val pos: (Position, Position)) extends PSetLiteral with PEmptyCollectionLiteral

case class PExplicitSet(args: Seq[PExp])(val pos: (Position, Position)) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral {
  override val opName = "Multiset#Multiset"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else PMultisetType(pType)()
}

case class PEmptyMultiset(override val pElementType: PType)(val pos: (Position, Position)) extends PMultiSetLiteral with PEmptyCollectionLiteral

case class PExplicitMultiset(override val args: Seq[PExp])(val pos: (Position, Position)) extends PMultiSetLiteral with PExplicitCollectionLiteral


/* ** Maps */

sealed trait PMapLiteral extends POpApp {
  override val opName = "Map#Map"

  def pKeyType: PType

  def pValueType: PType

  def pMapType(keyType: PType, valueType: PType): PType =
    if (keyType.isUnknown || valueType.isUnknown) PUnknown()()
    else PMapType(keyType, valueType)()
}

case class PEmptyMap(override val pKeyType: PType, override val pValueType: PType)(val pos: (Position, Position)) extends PMapLiteral {
  override val args = Seq()

  override val extraLocalTypeVariables: Set[PDomainType] =
    Set(pKeyType, pValueType) collect { case t: PDomainType if t.isTypeVar => t }

  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> pMapType(pKeyType, pValueType)
  ))
}

case class PExplicitMap(override val args: Seq[PMaplet])(val pos: (Position, Position)) extends PMapLiteral {
  override def pKeyType: PType = args.head.key.typ

  override def pValueType: PType = args.head.value.typ

  override def signatures: List[PTypeSubstitution] = List(
    args.indices.map {
      case 0 => POpApp.pResS -> POpApp.pArg(0)
      case n => POpApp.pArgS(n) -> POpApp.pArg(0)
    }.toMap
  )
}

/**
  * A key-value pair (i.e., an entry of an `PExplicitMap`) is
  * considered to be a singleton map literal itself.
  */
case class PMaplet(key: PExp, value: PExp)(val pos: (Position, Position)) extends PMapLiteral {
  override def pKeyType: PType = key.typ

  override def pValueType: PType = value.typ

  override def args: Seq[PExp] = Seq(key, value)

  override def signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pResS -> PMapType(POpApp.pArg(0), POpApp.pArg(1))()
  ))
}

case class PMapDomain(base: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#domain"
  override val args = Seq(base)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> PMapType(keyType, valueType)(),
    POpApp.pResS -> PSetType(keyType)()
  ))
}

case class PMapRange(base: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#range"
  override val args = Seq(base)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> PMapType(keyType, valueType)(),
    POpApp.pResS -> PSetType(valueType)()
  ))
}


///////////////////////////////////////////////////////////////////////////
// Statements
trait PStmt extends PNode {
  /**
    * Returns a list of all actual statements contained in this statement.  That
    * is, all statements except `Seqn`, including statements in the body of loops, etc.
    */
  def childStmts: Seq[PStmt] = {
    this match {
      case PSeqn(ss) => ss
      case PIf(_, thn, els) => Seq(this, thn, els)
      case PWhile(_, _, body) => Seq(this, body)
      case _ => Seq(this)
    }
  }
}

case class PAnnotatedStmt(stmt: PStmt, annotation: (String, Seq[String]))(val pos: (Position, Position)) extends PStmt

case class PSeqn(ss: Seq[PStmt])(val pos: (Position, Position)) extends PStmt with PScope

/**
  * PSeqn representing the expanded body of a statement macro.
  * Unlike a normal PSeqn, it does not represent its own scope.
  * Is created only temporarily during macro expansion and eliminated (i.e., expanded into the surrounding scope)
  * before translation.
  */
case class PMacroSeqn(ss: Seq[PStmt])(val pos: (Position, Position)) extends PStmt

case class PFold(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PUnfold(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PPackageWand(wand: PExp, proofScript: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PApplyWand(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PExhale(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssert(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssume(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PInhale(e: PExp)(val pos: (Position, Position)) extends PStmt

/** Can also represent a method call or statement macro with no `:=` when `targets` is empty. */
case class PAssign(targets: Seq[PAssignTarget], rhs: PExp)(val pos: (Position, Position)) extends PStmt

case class PIf(cond: PExp, thn: PSeqn, els: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PWhile(cond: PExp, invs: Seq[PExp], body: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PVars(vars: Seq[PLocalVarDecl], init: Option[PExp])(val pos: (Position, Position)) extends PStmt

case class PLabel(idndef: PIdnDef, invs: Seq[PExp])(val pos: (Position, Position)) extends PStmt with PLocalDeclaration

case class PGoto(targets: PIdnUse)(val pos: (Position, Position)) extends PStmt

case class PTypeVarDecl(idndef: PIdnDef)(val pos: (Position, Position)) extends PLocalDeclaration

case class PDefine(idndef: PIdnDef, parameters: Option[Seq[PIdnDef]], body: PNode)(val pos: (Position, Position)) extends PStmt with PLocalDeclaration

case class PSkip()(val pos: (Position, Position)) extends PStmt

case class PQuasihavoc(lhs: Option[PExp], e: PExp)(val pos: (Position, Position)) extends PStmt

case class PQuasihavocall(vars: Seq[PLogicalVarDecl], lhs: Option[PExp], e: PExp)(val pos: (Position, Position)) extends PStmt with PScope

/* new(f1, ..., fn) or new(*) */
case class PNewExp(fields: Option[Seq[PIdnUse]])(val pos: (Position, Position)) extends PExp {
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

trait PDeclaration extends PNode with PEntity {
  def idndef: PIdnDef
}

sealed trait PUnnamedTypedDeclaration extends PNode {
  def typ: PType
}

trait PGlobalDeclaration extends PDeclaration

trait PLocalDeclaration extends PDeclaration

trait PUniversalDeclaration extends PDeclaration

sealed trait PTypedDeclaration extends PDeclaration with PUnnamedTypedDeclaration

abstract class PErrorEntity extends PEntity {
  def name: String
}

trait PAnnotated {
  def annotations: Seq[(String, Seq[String])]
}

// a member (like method or axiom) that is its own name scope
trait PMember extends PScope with PAnnotated {
  def declares: Seq[PGlobalDeclaration]
}

/** Anything that is a PMember and declares only a single thing (itself) */
trait PSingleMember extends PMember with PGlobalDeclaration {
  override def declares = Seq(this)
}

trait PAnyFunction extends PSingleMember with PTypedDeclaration {
  def idndef: PIdnDef

  def formalArgs: Seq[PAnyFormalArgDecl]

  def resultType: PType
  override def typ: PFunctionType = PFunctionType(formalArgs.map(_.typ), resultType)
}

case class PProgram(imports: Seq[PImport], macros: Seq[PDefine], domains: Seq[PDomain], fields: Seq[PFields], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod], extensions: Seq[PExtender], errors: Seq[ParseReport])(val pos: (Position, Position)) extends PNode

abstract class PImport() extends PNode

case class PLocalImport(file: String)(val pos: (Position, Position)) extends PImport()

case class PStandardImport(file: String)(val pos: (Position, Position)) extends PImport()

case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalReturnDecl], pres: Seq[PExp], posts: Seq[PExp], body: Option[PStmt])
                  (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PSingleMember {
  def deepCopy(idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, formalReturns: Seq[PFormalReturnDecl] = this.formalReturns, pres: Seq[PExp] = this.pres, posts: Seq[PExp] = this.posts, body: Option[PStmt] = this.body): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(idndef, formalArgs, formalReturns, pres, posts, body)(p.pos, p.annotations)
    }).execute[PMethod](this)
  }

  def deepCopyWithNameSubstitution(idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, formalReturns: Seq[PFormalReturnDecl] = this.formalReturns, pres: Seq[PExp] = this.pres, posts: Seq[PExp] = this.posts, body: Option[PStmt] = this.body)
                                  (idn_generic_name: String, idn_substitution: String): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(idndef, formalArgs, formalReturns, pres, posts, body)(p.pos, p.annotations)
      case p@PIdnDef(name) if name == idn_generic_name => PIdnDef(idn_substitution)(p.pos)
      case p@PIdnUse(name) if name == idn_generic_name => PIdnUse(idn_substitution)(p.pos)
    }).execute[PMethod](this)
  }
}

case class PDomain(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], funcs: Seq[PDomainFunction], axioms: Seq[PAxiom], interpretations: Option[Map[String, String]])
                  (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PSingleMember
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], resultType: PType, pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp])
                    (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PAnyFunction {
  def deepCopy(idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, resultType: PType = this.resultType, pres: Seq[PExp] = this.pres, posts: Seq[PExp] = this.posts, body: Option[PExp] = this.body): PFunction = {
    StrategyBuilder.Slim[PNode]({
      case p: PFunction => PFunction(idndef, formalArgs, resultType, pres, posts, body)(p.pos, p.annotations)
    }).execute[PFunction](this)
  }
}

case class PDomainFunction(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl], resultType: PType, unique: Boolean, interpretation: Option[String])
                          (val domainName:PIdnUse)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PAnyFunction
case class PAxiom(idndef: Option[PIdnDef], exp: PExp)(val domainName:PIdnUse)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PScope
case class PFields(fields: Seq[PFieldDecl])(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PMember {
  override def declares: Seq[PGlobalDeclaration] = fields
}
case class PPredicate(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: Option[PExp])
                     (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PSingleMember with PTypedDeclaration {
  val typ = PPredicateType()()
}

case class PDomainFunction1(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl], typ: PType, unique: Boolean, interpretation: Option[String])(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])])
case class PAxiom1(idndef: Option[PIdnDef], exp: PExp)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])])

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


/**
  * Utility methods for parser parserAST nodes.
  */
object Nodes {

  /**
    * See PNode.subnodes.
    */
  def subnodes(n: PNode): Seq[PNode] = {
    n match {
      case PIdnDef(_) => Nil
      case PIdnUse(_) => Nil
      case PUnnamedFormalArgDecl(typ) => Seq(typ)
      case PFormalArgDecl(idndef, typ) => Seq(idndef, typ)
      case PFormalReturnDecl(idndef, typ) => Seq(idndef, typ)
      case PLogicalVarDecl(idndef, typ) => Seq(idndef, typ)
      case PLocalVarDecl(idndef, typ) => Seq(idndef, typ)
      case PFieldDecl(idndef, typ) => Seq(idndef, typ)
      case PPrimitiv(_) => Nil
      case PDomainType(domain, args) => Seq(domain) ++ args
      case PSeqType(elemType) => Seq(elemType)
      case PSetType(elemType) => Seq(elemType)
      case PMultisetType(elemType) => Seq(elemType)
      case PMapType(keyType, valueType) => Seq(keyType, valueType)
      case PUnknown() => Nil
      case PPredicateType() => Nil
      case PWandType() => Nil
      case PFunctionType(args, result) => args ++ Seq(result)
      case PBinExp(left, _, right) => Seq(left, right)
      case PMagicWandExp(left, right) => Seq(left, right)
      case PUnExp(_, exp) => Seq(exp)
      case PTrigger(exp) => exp
      case PIntLit(_) => Nil
      case PBoolLit(_) => Nil
      case PNullLit() => Nil
      case PResultLit() => Nil
      case PFieldAccess(rcv, field) => Seq(rcv, field)
      case PCall(func, args, optType) => Seq(func) ++ args ++ (optType match {
        case Some(t) => Seq(t)
        case None => Nil
      })
      case PUnfolding(acc, exp) => Seq(acc, exp)
      case PApplying(wand, exp) => Seq(wand, exp)
      case PExists(vars, triggers, exp) => vars ++ triggers ++ Seq(exp)
      case PLabelledOld(id, e) => Seq(id, e)
      case po: POldExp => Seq(po.e)
      case PLet(exp, nestedScope) => Seq(exp, nestedScope)
      case PLetNestedScope(variable, body) => Seq(variable, body)
      case PForall(vars, triggers, exp) => vars ++ triggers ++ Seq(exp)
      case PForPerm(vars, res, expr) => vars :+ res :+ expr
      case PCondExp(cond, thn, els) => Seq(cond, thn, els)
      case PInhaleExhaleExp(in, ex) => Seq(in, ex)
      case PCurPerm(loc) => Seq(loc)
      case PNoPerm() => Nil
      case PFullPerm() => Nil
      case PWildcard() => Nil
      case PEpsilon() => Nil
      case PAccPred(loc, perm) => Seq(loc, perm)
      case PEmptySeq(_) => Nil
      case PSeqIndex(seq, idx) => Seq(seq, idx)
      case PExplicitSeq(elems) => elems
      case PRangeSeq(low, high) => Seq(low, high)
      case PSeqTake(seq, nn) => Seq(seq, nn)
      case PSeqDrop(seq, nn) => Seq(seq, nn)
      case PSeqUpdate(seq, idx, elem) => Seq(seq, idx, elem)
      case PLookup(seq, idx) => Seq(seq, idx)
      case PUpdate(seq, idx, elem) => Seq(seq, idx, elem)
      case PSize(seq) => Seq(seq)
      case PEmptySet(t) => Seq(t)
      case PExplicitSet(elems) => elems
      case PEmptyMultiset(t) => Seq(t)
      case PExplicitMultiset(elems) => elems
      case PEmptyMap(k, v) => Seq(k, v)
      case PExplicitMap(elems) => elems
      case PMapRange(base) => Seq(base)
      case PMapDomain(base) => Seq(base)
      case PMaplet(key, value) => Seq(key, value)
      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
      case PPackageWand(exp, proofScript) => Seq(exp, proofScript)
      case PApplyWand(exp) => Seq(exp)
      case PExhale(exp) => Seq(exp)
      case PAssert(exp) => Seq(exp)
      case PInhale(exp) => Seq(exp)
      case PAssume(exp) => Seq(exp)
      case PNewExp(fields) => fields.getOrElse(Seq())
      case PLabel(name, invs) => Seq(name) ++ invs
      case PGoto(label) => Seq(label)
      case PAssign(targets, rhs) => targets ++ Seq(rhs)
      case PIf(cond, thn, els) => Seq(cond, thn, els)
      case PWhile(cond, invs, body) => Seq(cond) ++ invs ++ Seq(body)
      case PVars(vars, init) => vars ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PProgram(_, _, domains, fields, functions, predicates, methods, extensions, _) =>
        domains ++ fields ++ functions ++ predicates ++ methods ++ extensions
      case PLocalImport(_) =>
        Seq()
      case PStandardImport(_) => Seq()
      case PDomain(idndef, typVars, funcs, axioms, _) => Seq(idndef) ++ typVars ++ funcs ++ axioms
      case PFields(fields) => fields
      case PMethod(idndef, args, rets, pres, posts, body) =>
        Seq(idndef) ++ args ++ rets ++ pres ++ posts ++ body.toSeq
      case PFunction(name, args, typ, pres, posts, body) =>
        Seq(name) ++ args ++ Seq(typ) ++ pres ++ posts ++ body
      case PDomainFunction(name, args, typ, _, _) =>
        Seq(name) ++ args ++ Seq(typ)
      case PPredicate(name, args, body) =>
        Seq(name) ++ args ++ body
      case PAxiom(idndef, exp) => (if (idndef.isDefined) Seq(idndef.get) else Nil) ++ Seq(exp)
      case PTypeVarDecl(name) => Seq(name)
      case PDefine(idndef, optArgs, body) => Seq(idndef) ++ optArgs.getOrElse(Nil) ++ Seq(body)
      case PQuasihavoc(lhs, e) => lhs.toSeq :+ e
      case PQuasihavocall(vars, lhs, e) => vars ++ lhs.toSeq :+ e
      case PAnnotatedExp(e, _) => Seq(e)
      case PAnnotatedStmt(s, _) => Seq(s)
      case t: PExtender => t.getSubnodes()
      case _: PSkip => Nil
    }
  }
}
