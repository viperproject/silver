// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import viper.silver.ast.utility.{HasSemanticTokens, SemanticHighlight, TokenType, Visitor}
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder}
import viper.silver.ast.{Exp, FilePosition, MagicWandOp, Member, NoPosition, Position, Stmt, Type}
import viper.silver.parser.TypeHelper._
import viper.silver.verifier.ParseReport

import scala.collection.Set
import scala.language.implicitConversions

trait Where {
  val pos: (Position, Position)
  def filePos: Option[(FilePosition, FilePosition)] = pos match {
    case (fp1: FilePosition, fp2: FilePosition) => Some((fp1, fp2))
    case _ => None
  }
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
  val Int = PPrimitiv(PKeyword("Int")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Bool = PPrimitiv(PKeyword("Bool")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Perm = PPrimitiv(PKeyword("Perm")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Ref = PPrimitiv(PKeyword("Ref")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Pred = PPredicateType()((NoPosition, NoPosition))
  val Wand = PWandType()((NoPosition, NoPosition))
  def MakeSet(typ: PType) = PSetType(PKeyword("Set")(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
  def MakeSeq(typ: PType) = PSeqType(PKeyword("Seq")(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
  def MakeMap(key: PType, value: PType) = PMapType(PKeyword("Map")(NoPosition, NoPosition), key, value)((NoPosition, NoPosition))
  def MakeMultiset(typ: PType) = PMultisetType(PKeyword("Multiset")(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
}

// Identifiers (uses and definitions)
trait PIdentifier {
  def name: String
}

case class PIdnDef(name: String)(val pos: (Position, Position)) extends PNode with PIdentifier

case class PIdnUse(name: String)(val pos: (Position, Position)) extends PExp with PIdentifier with HasSemanticTokens {
  var decl: PDeclaration = null
  /* Should be set during resolving. Intended to preserve information
   * that is needed by the translator.
   */
  override val typeSubstitutions = List(PTypeSubstitution.id)

  def forceSubstitution(ts: PTypeSubstitution) = {
    typ = typ.substitute(ts)
    assert(typ.isGround)
  }

  override def semanticTokens: Seq[SemanticHighlight] = (decl, filePos) match {
    case (_: PLocalVarDecl, Some(fp)) => Seq(SemanticHighlight(fp._1, fp._2, TokenType.Variable))
    case (_: PFormalArgDecl, Some(fp)) => Seq(SemanticHighlight(fp._1, fp._2, TokenType.Parameter))
    case _ => Seq()
  }
}

case class PKeyword(keyword: String)(val pos: (Position, Position)) extends PIsSemanticToken {
  override def tokenType = TokenType.Keyword
}
object PKeyword {
  def empty = PKeyword("")(NoPosition, NoPosition)
}

case class POperator(operator: String)(val pos: (Position, Position)) extends PNode with PIsSemanticToken {
  override def tokenType = TokenType.Operator
}

trait PAnyFormalArgDecl extends PNode with PUnnamedTypedDeclaration

case class PUnnamedFormalArgDecl(var typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl

/* Formal arguments.
 * [2014-11-13 Malte] Changed type to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PFormalArgDecl(idndef: PIdnDef, var typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl with PTypedDeclaration with PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Parameter
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


case class PPrimitiv(name: PKeyword)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType {
  override def substitute(ts: PTypeSubstitution): PType = this

  override val subNodes = Seq()

  override def toString = name.keyword

  override def isValidOrUndeclared = true
}

case class PDomainType(domain: PIdnUse, args: Seq[PType])(val pos: (Position, Position)) extends PGenericType with HasSemanticTokens {
  val genericName = domain.name
  override val typeArguments = args //if (kind==PDomainTypeKinds.Domain)
  var kind: PDomainTypeKinds.Kind = PDomainTypeKinds.Unresolved
  override val subNodes = args

  /* This class is also used to represent type variables, as they cannot
   * be distinguished syntactically from domain types without generic arguments.
   * For type variables, we have args.length = 0
   */
  def isTypeVar = kind == PDomainTypeKinds.TypeVar

  override def semanticTokens: Seq[SemanticHighlight] = domain.filePos.flatMap(pos => kind match {
    case PDomainTypeKinds.TypeVar => Some(SemanticHighlight(pos._1, pos._2, TokenType.TypeParameter))
    case PDomainTypeKinds.Domain => Some(SemanticHighlight(pos._1, pos._2, TokenType.Interface))
    case _ => None
  }).toSeq

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

case class PSeqType(seq: PKeyword, elementType: PType)(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Seq"

  override def substitute(map: PTypeSubstitution) = PSeqType(seq, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PSetType(set: PKeyword, elementType: PType)(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Set"

  override def substitute(map: PTypeSubstitution) = PSetType(set, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PMultisetType(multiset: PKeyword, elementType: PType)(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"

  override def substitute(map: PTypeSubstitution) = PMultisetType(multiset, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMultisetType = copy(elementType = s.head)(pos)
}

case class PMapType(map: PKeyword, keyType: PType, valueType: PType)(val pos: (Position, Position)) extends PType with PGenericType {
  override val genericName = "Map"
  override val subNodes = Seq(keyType, valueType)
  override val typeArguments = Seq(keyType, valueType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)

  override def substitute(map: PTypeSubstitution) = PMapType(this.map, keyType.substitute(map), valueType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMapType = copy(keyType = s.head, valueType = s(1))(pos)
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

case class PMagicWandExp(override val left: PExp, wand: POperator, override val right: PExp)(val posi: (Position, Position)) extends PBinExp(left, wand, right)(posi) with PResourceAccess

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

trait POpAppKeyword extends POpApp {
  def op: POperator
  override def opName = op.operator
}

case class PCall(func: PIdnUse, args: Seq[PExp], typeAnnotated: Option[PType] = None)(val pos: (Position, Position)) extends POpApp with PLocationAccess with HasSemanticTokens {
  override val idnuse = func
  override val opName = func.name

  override def semanticTokens: Seq[SemanticHighlight] = (func.filePos, function, extfunction) match {
    case (_, null, null) => Seq()
    case (Some(fp), _: PDomainFunction, null) => Seq(SemanticHighlight(fp._1, fp._2, TokenType.Function))
    case (Some(fp), _: PFunction, null) => Seq(SemanticHighlight(fp._1, fp._2, TokenType.Function))
    case (Some(fp), null, _) => Seq(SemanticHighlight(fp._1, fp._2, TokenType.Struct))
    case _ => Seq()
  }

  override def signatures = if (function != null && function.formalArgs.size == args.size) (function match {
    case _: PFunction => List(
      new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgs(i).typ) :+ (POpApp.pRes.domain.name -> function.typ))
    )
    case pdf: PDomainFunction =>
      List(
        new PTypeSubstitution(
          args.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgs(i).typ.substitute(domainTypeRenaming.get)) :+
            (POpApp.pRes.domain.name -> pdf.typ.substitute(domainTypeRenaming.get)))
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

class PBinExp(val left: PExp, val op: POperator, val right: PExp)(val pos: (Position, Position)) extends POpAppKeyword {

  override val args = Seq(left, right)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    op.operator match {
      case "++" | "union" | "intersection" | "setminus" | "subset" | "in" => Set(extraElementType)
      case _ => Set()
    }
  val signatures: List[PTypeSubstitution] = op.operator match {
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
      Map(POpApp.pArgS(1) -> MakeSet(POpApp.pArg(0)), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> MakeSeq(POpApp.pArg(0)), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> MakeMultiset(POpApp.pArg(0)), POpApp.pResS -> Int),
      Map(POpApp.pArgS(1) -> MakeMap(POpApp.pArg(0), extraElementType), POpApp.pResS -> Bool)
    )
    case "++" => List(
      Map(POpApp.pArgS(0) -> MakeSeq(extraElementType), POpApp.pArgS(1) -> MakeSeq(extraElementType), POpApp.pResS -> MakeSeq(extraElementType))
    )
    case "union" | "intersection" | "setminus" => List(
      Map(POpApp.pArgS(0) -> MakeSet(extraElementType), POpApp.pArgS(1) -> MakeSet(extraElementType), POpApp.pResS -> MakeSet(extraElementType)),
      Map(POpApp.pArgS(0) -> MakeMultiset(extraElementType), POpApp.pArgS(1) -> MakeMultiset(extraElementType), POpApp.pResS -> MakeMultiset(extraElementType))
    )
    case "subset" => List(
      Map(POpApp.pArgS(0) -> MakeSet(extraElementType), POpApp.pArgS(1) -> MakeSet(extraElementType), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> MakeMultiset(extraElementType), POpApp.pArgS(1) -> MakeMultiset(extraElementType), POpApp.pResS -> Bool)
    )
    case _ => sys.error(s"internal error - unknown binary operator \"${op.operator}\"")
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
      other.op.operator.equals(this.op.operator) && other.right.equals(this.right) && other.left.equals(this.left)
    } else false
  }

  override def hashCode(): Int = viper.silver.utility.Common.generateHashCode(left, op.operator, right)
}

object PBinExp {

  def apply(left: PExp, op: POperator, right: PExp)(pos: (Position, Position)): PBinExp =
    new PBinExp(left, op, right)(pos)

  def unapply(arg: PBinExp): Option[(PExp, POperator, PExp)] = Some(arg.left, arg.op, arg.right)
}

case class PUnExp(op: POperator, exp: PExp)(val pos: (Position, Position)) extends POpAppKeyword {
  override val args = Seq(exp)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    op.operator match {
      case "++" | "union" | "intersection" | "setminus" | "subset" | "in" => Set(extraElementType)
      case _ => Set()
    }
  override val signatures: List[PTypeSubstitution] = op.operator match {
    case "-" => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pResS -> Int),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pResS -> Perm)
    )
    case "!" => List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool)
    )
    case _ => sys.error(s"internal error - unknown unary operator ${op.operator}")
  }
}

case class PCondExp(cond: PExp, q: POperator, thn: PExp, c: POperator, els: PExp)(val pos: (Position, Position)) extends POpApp {
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

case class PResultLit(result: PKeyword)(val pos: (Position, Position)) extends PSimpleLiteral

case class PBoolLit(keyword: PKeyword, b: Boolean)(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Bool
}

case class PNullLit(nul: PKeyword)(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Ref
}

sealed trait PHeapOpApp extends POpApp

sealed trait PResourceAccess extends PHeapOpApp

trait PLocationAccess extends PResourceAccess {
  def idnuse: PIdnUse
}

case class PFieldAccess(rcv: PExp, idnuse: PIdnUse)(val pos: (Position, Position)) extends PLocationAccess with HasSemanticTokens {
  override final val opName = "."
  override final val args = Seq(rcv)

  override def semanticTokens: Seq[SemanticHighlight] = idnuse.filePos.map(fp => SemanticHighlight(fp._1, fp._2, TokenType.Property)).toSeq

  override def signatures =
    if (Set(rcv.typ, idnuse.typ).forall(_.isValidOrUndeclared))
      List(PTypeSubstitution(Map(POpApp.pArgS(0) -> Ref, POpApp.pResS -> idnuse.typ)))
    else
      List()
  //setType()
}

case class PPredicateAccess(args: Seq[PExp], idnuse: PIdnUse)(val pos: (Position, Position)) extends PLocationAccess {
  override final val opName = "acc"
  var predicate: PPredicate = null

  override def signatures = if (predicate == null) List() else
    List(new PTypeSubstitution(
      args.indices.map(i => POpApp.pArg(i).domain.name -> predicate.formalArgs(i).typ) :+
        (POpApp.pRes.domain.name -> Pred)))
}

case class PUnfolding(op: POperator, acc: PAccPred, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp with POpAppKeyword {
  override val args = Seq(acc, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)))
}

case class PApplying(applying: PKeyword, wand: PExp, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp {
  override val opName = "applying"
  override val args = Seq(wand, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Wand, POpApp.pResS -> POpApp.pArg(1)))
}

sealed trait PBinder extends PExp {
  def body: PExp

  var _typeSubstitutions: List[PTypeSubstitution] = null

  override def typeSubstitutions = _typeSubstitutions

  override def forceSubstitution(ts: PTypeSubstitution) = {
    _typeSubstitutions = List(ts)
    typ = typ.substitute(ts)
    body.forceSubstitution(ts)
  }
}

sealed trait PQuantifier extends PBinder with PScope {
  def vars: Seq[PFormalArgDecl]

  def triggers: Seq[PTrigger]
}

case class PExists(exists: PKeyword, vars: Seq[PFormalArgDecl], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForall(forall: PKeyword, vars: Seq[PFormalArgDecl], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForPerm(forperm: PKeyword, vars: Seq[PFormalArgDecl], accessRes: PResourceAccess, body: PExp)(val pos: (Position, Position)) extends PQuantifier {
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
case class PLet(exp: PExp, nestedScope: PLetNestedScope)(val pos: (Position, Position)) extends PBinder {
  override val body = nestedScope.body

  override def forceSubstitution(ts: PTypeSubstitution) = {
    super.forceSubstitution(ts)
    exp.forceSubstitution(ts)
    body.forceSubstitution(ts)
    nestedScope.variable.typ = exp.typ
  }
}

case class PLetNestedScope(variable: PFormalArgDecl, body: PExp)(val pos: (Position, Position)) extends PNode with PScope

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

case class PAccPred(op: POperator, loc: PLocationAccess, perm: PExp)(val pos: (Position, Position)) extends POpAppKeyword {
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

case class PLabelledOld(label: PIdnUse, e: PExp)(val pos: (Position, Position)) extends POldExp with HasSemanticTokens {
  override val opName = "old#labeled"
  override def semanticTokens: Seq[SemanticHighlight] = label.filePos.map(fp => SemanticHighlight(fp._1, fp._2, TokenType.Event)).toSeq
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

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSeq(pType)
}

case class PEmptySeq(pElementType: PType)(val pos: (Position, Position)) extends PSeqLiteral with PEmptyCollectionLiteral

case class PExplicitSeq(override val args: Seq[PExp])(val pos: (Position, Position)) extends PSeqLiteral with PExplicitCollectionLiteral

case class PRangeSeq(low: PExp, high: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#RangeSeq"
  override val args = Seq(low, high)
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(Int)))
}

case class PSeqIndex(seq: PExp, idx: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#At"
  override val args = Seq(seq, idx)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> MakeSeq(POpApp.pRes),
      POpApp.pArgS(1) -> Int)
  )
}

case class PLookup(base: PExp, idx: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)

  override val opName = "lookup"
  override val args = Seq(base, idx)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(POpApp.pRes), POpApp.pArgS(1) -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, POpApp.pRes))
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
      POpApp.pArgS(0) -> MakeSeq(elementType),
      POpApp.pArgS(1) -> Int,
      POpApp.pResS -> MakeSeq(elementType)
    ))
}

case class PSeqDrop(seq: PExp, n: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#Drop"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq, n)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> MakeSeq(elementType),
      POpApp.pArgS(1) -> Int,
      POpApp.pResS -> MakeSeq(elementType)
    ))
}

case class PSeqUpdate(seq: PExp, idx: PExp, elem: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#update"
  val elementType = POpApp.pArg(2)
  override val args = Seq(seq, idx, elem)
  override val signatures: List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0) -> MakeSeq(elementType),
      POpApp.pArgS(1) -> Int,
      POpApp.pResS -> MakeSeq(elementType)
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
    Map(POpApp.pArgS(0) -> MakeSeq(elementType), POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(elementType)),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, elementType), POpApp.pResS -> MakeMap(keyType, elementType))
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
    Map(POpApp.pArgS(0) -> MakeSeq(elementType), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> MakeSet(elementType), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> MakeMultiset(elementType), POpApp.pResS -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, elementType), POpApp.pResS -> Int)
  )
}

sealed trait PSetLiteral extends PCollectionLiteral {
  override val opName = "Set#Set"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSet(pType)
}

case class PEmptySet(pElementType: PType)(val pos: (Position, Position)) extends PSetLiteral with PEmptyCollectionLiteral

case class PExplicitSet(args: Seq[PExp])(val pos: (Position, Position)) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral {
  override val opName = "Multiset#Multiset"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeMultiset(pType)
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
    else MakeMap(keyType, valueType)
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
    POpApp.pResS -> MakeMap(POpApp.pArg(0), POpApp.pArg(1))
  ))
}

case class PMapDomain(base: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#domain"
  override val args = Seq(base)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(keyType)
  ))
}

case class PMapRange(base: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = PTypeVar("#K")
  val valueType: PDomainType = PTypeVar("#E")

  override val opName = "Map#range"
  override val args = Seq(base)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType, valueType)

  override val signatures: List[PTypeSubstitution] = List(Map(
    POpApp.pArgS(0) -> MakeMap(keyType, valueType),
    POpApp.pResS -> MakeSet(valueType)
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
      case PIf(_, _, thn, _, els) => Seq(this, thn, els)
      case PWhile(_, _, _, body) => Seq(this, body)
      case _ => Seq(this)
    }
  }
}

case class PAnnotatedStmt(stmt: PStmt, annotation: (String, Seq[String]))(val pos: (Position, Position)) extends PStmt

case class PSeqn(ss: Seq[PStmt])(val pos: (Position, Position)) extends PStmt with PScope

case class PFold(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PUnfold(e: PExp)(val pos: (Position, Position)) extends PStmt

case class PPackageWand(pckg: PKeyword, wand: PExp, proofScript: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PApplyWand(apply: PKeyword, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PExhale(exhale: PKeyword, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssert(assert: PKeyword, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssume(assume: PKeyword, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PInhale(inhale: PKeyword, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PVarAssign(idnuse: PIdnUse, rhs: PExp)(val pos: (Position, Position)) extends PStmt

case class PFieldAssign(fieldAcc: PFieldAccess, rhs: PExp)(val pos: (Position, Position)) extends PStmt

case class PMacroAssign(call: PCall, exp: PExp)(val pos: (Position, Position)) extends PStmt

case class PIf(keyword: PKeyword, cond: PExp, thn: PSeqn, elsKw: Option[PKeyword], els: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PWhile(keyword: PKeyword, cond: PExp, invs: Seq[(PKeyword, PExp)], body: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PLocalVarDecl(keyword: PKeyword, idndef: PIdnDef, typ: PType, init: Option[PExp])(val pos: (Position, Position)) extends PStmt with PTypedDeclaration with PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Variable
}

case class PGlobalVarDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PTypedDeclaration with PUniversalDeclaration

case class PMethodCall(targets: Seq[PIdnUse], method: PIdnUse, args: Seq[PExp])(val pos: (Position, Position)) extends PStmt

case class PLabel(label: PKeyword, idndef: PIdnDef, invs: Seq[(PKeyword, PExp)])(val pos: (Position, Position)) extends PStmt with PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Event
}

case class PGoto(targets: PIdnUse)(val pos: (Position, Position)) extends PStmt with HasSemanticTokens {
  override def semanticTokens: Seq[SemanticHighlight] = targets.filePos.map(fp => SemanticHighlight(fp._1, fp._2, TokenType.Event)).toSeq
}

case class PTypeVarDecl(idndef: PIdnDef)(val pos: (Position, Position)) extends PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.TypeParameter
}

case class PMacroRef(idnuse: PIdnUse)(val pos: (Position, Position)) extends PStmt

case class PDefine(define: PKeyword, idndef: PIdnDef, parameters: Option[Seq[PIdnDef]], body: PNode)(val pos: (Position, Position)) extends PStmt with PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Macro
}

case class PSkip()(val pos: (Position, Position)) extends PStmt

case class PQuasihavoc(quasihavoc: PKeyword, lhs: Option[(PExp, POperator)], e: PExp)(val pos: (Position, Position)) extends PStmt

case class PQuasihavocall(quasihavocall: PKeyword, vars: Seq[PFormalArgDecl], colons: POperator, lhs: Option[(PExp, POperator)], e: PExp)(val pos: (Position, Position)) extends PStmt with PScope

sealed trait PNewStmt extends PStmt {
  def target: PIdnUse
}

/* x := new(f1, ..., fn) */
case class PRegularNewStmt(target: PIdnUse, fields: Seq[PIdnUse])(val pos: (Position, Position)) extends PNewStmt

/* x := new(*) */
case class PStarredNewStmt(target: PIdnUse)(val pos: (Position, Position)) extends PNewStmt

object PNewStmt {
  def apply(target: PIdnUse): PStarredNewStmt = PStarredNewStmt(target)(target.pos)

  def apply(target: PIdnUse, fields: Seq[PIdnUse]): PRegularNewStmt = PRegularNewStmt(target, fields)(target.pos)

  def apply(target: PIdnUse, fields: Option[Seq[PIdnUse]]): PNewStmt = fields match {
    case None => PStarredNewStmt(target)(target.pos)
    case Some(fs) => PRegularNewStmt(target, fs)(target.pos)
  }

  def unapply(s: PNewStmt): Option[(PIdnUse, Option[Seq[PIdnUse]])] = s match {
    case PRegularNewStmt(target, fields) => Some((target, Some(fields)))
    case PStarredNewStmt(_) => Some((s.target, None))
  }
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

trait PSemanticDeclaration extends HasSemanticTokens with PDeclaration {
  def tokenType: TokenType.TokenType
  override def semanticTokens: Seq[SemanticHighlight] = idndef.filePos.map(fp => SemanticHighlight(fp._1, fp._2, tokenType)).toSeq
}

trait PIsSemanticToken extends PNode with HasSemanticTokens {
  def tokenType: TokenType.TokenType
  override def semanticTokens: Seq[SemanticHighlight] = filePos.map(fp => SemanticHighlight(fp._1, fp._2, tokenType)).toSeq
}

abstract class PErrorEntity extends PEntity {
  def name: String
}


// a member (like method or axiom) that is its own name scope
trait PMember extends PDeclaration with PScope

trait PAnyFunction extends PMember with PGlobalDeclaration with PTypedDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Function
  def formalArgs: Seq[PAnyFormalArgDecl]
}

case class PProgram(imports: Seq[PImport], macros: Seq[PDefine], domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod], extensions: Seq[PExtender], errors: Seq[ParseReport])(val pos: (Position, Position)) extends PNode {
  var imported: Array[ResolvedImport] = null
}

abstract class PImport() extends PNode

case class PLocalImport(imprt: PKeyword, file: String)(val pos: (Position, Position)) extends PImport()

case class PStandardImport(imprt: PKeyword, file: String)(val pos: (Position, Position)) extends PImport()

case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[(PKeyword, PExp)], posts: Seq[(PKeyword, PExp)], body: Option[PStmt])
                  (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PMember with PGlobalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Method

  def deepCopy(idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, formalReturns: Seq[PFormalArgDecl] = this.formalReturns, pres: Seq[(PKeyword, PExp)] = this.pres, posts: Seq[(PKeyword, PExp)] = this.posts, body: Option[PStmt] = this.body): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(idndef, formalArgs, formalReturns, pres, posts, body)(p.pos, p.annotations)
    }).execute[PMethod](this)
  }

  def deepCopyWithNameSubstitution(idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, formalReturns: Seq[PFormalArgDecl] = this.formalReturns, pres: Seq[(PKeyword, PExp)] = this.pres, posts: Seq[(PKeyword, PExp)] = this.posts, body: Option[PStmt] = this.body)
                                  (idn_generic_name: String, idn_substitution: String): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(idndef, formalArgs, formalReturns, pres, posts, body)(p.pos, p.annotations)
      case p@PIdnDef(name) if name == idn_generic_name => PIdnDef(idn_substitution)(p.pos)
      case p@PIdnUse(name) if name == idn_generic_name => PIdnUse(idn_substitution)(p.pos)
    }).execute[PMethod](this)
  }
}

case class PDomain(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], funcs: Seq[PDomainFunction], axioms: Seq[PAxiom], interpretations: Option[Map[String, String]])
                  (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PMember with PGlobalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Interface
}
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[(PKeyword, PExp)], posts: Seq[(PKeyword, PExp)], body: Option[PExp])
                    (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PAnyFunction {
  def deepCopy(idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, typ: PType = this.typ, pres: Seq[(PKeyword, PExp)] = this.pres, posts: Seq[(PKeyword, PExp)] = this.posts, body: Option[PExp] = this.body): PFunction = {
    StrategyBuilder.Slim[PNode]({
      case p: PFunction => PFunction(idndef, formalArgs, typ, pres, posts, body)(p.pos, p.annotations)
    }).execute[PFunction](this)
  }
}

case class PDomainFunction(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl], typ: PType, unique: Boolean, interpretation: Option[String])
                          (val domainName:PIdnUse)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PAnyFunction
case class PAxiom(idndef: Option[PIdnDef], exp: PExp)(val domainName:PIdnUse)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PScope
case class PField(field: PKeyword, idndef: PIdnDef, typ: PType)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PMember with PTypedDeclaration with PGlobalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Property
}
case class PPredicate(predicate: PKeyword, idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: Option[PExp])
                     (val pos: (Position, Position), val annotations: Seq[(String, Seq[String])]) extends PMember with PTypedDeclaration with PGlobalDeclaration with PSemanticDeclaration {
  val typ = PPredicateType()()
  override def tokenType = TokenType.Struct
}

case class PDomainFunction1(idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl], typ: PType, unique: Boolean, interpretation: Option[String])(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])])
case class PAxiom1(axiom: PKeyword, idndef: Option[PIdnDef], exp: PExp)(val pos: (Position, Position), val annotations: Seq[(String, Seq[String])])

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
      case PKeyword(_) => Nil
      case POperator(_) => Nil
      case PIdnDef(_) => Nil
      case PIdnUse(_) => Nil
      case PFormalArgDecl(idndef, typ) => Seq(idndef, typ)
      case PPrimitiv(keyword) => Seq(keyword)
      case PDomainType(domain, args) => Seq(domain) ++ args
      case PSeqType(seq, elemType) => Seq(seq, elemType)
      case PSetType(set, elemType) => Seq(set, elemType)
      case PMultisetType(multiset, elemType) => Seq(multiset, elemType)
      case PMapType(map, keyType, valueType) => Seq(map, keyType, valueType)
      case PUnknown() => Nil
      case PBinExp(left, op, right) => Seq(left, op, right)
      case PMagicWandExp(left, wand, right) => Seq(left, wand, right)
      case PUnExp(op, exp) => Seq(op, exp)
      case PTrigger(exp) => exp
      case PIntLit(_) => Nil
      case PBoolLit(keyword, _) => Seq(keyword)
      case PNullLit(nul) => Seq(nul)
      case PPredicateType() => Nil
      case PWandType() => Nil
      case PResultLit(result) => Seq(result)
      case PFieldAccess(rcv, field) => Seq(rcv, field)
      case PPredicateAccess(args, pred) => args ++ Seq(pred)
      case PCall(func, args, optType) => Seq(func) ++ args ++ (optType match {
        case Some(t) => Seq(t)
        case None => Nil
      })
      case PUnfolding(unfolding, acc, exp) => Seq(unfolding, acc, exp)
      case PApplying(applying, wand, exp) => Seq(applying, wand, exp)
      case PExists(exists, vars, triggers, exp) => Seq(exists) ++ vars ++ triggers ++ Seq(exp)
      case PLabelledOld(id, e) => Seq(id, e)
      case po: POldExp => Seq(po.e)
      case PLet(exp, nestedScope) => Seq(exp, nestedScope)
      case PLetNestedScope(variable, body) => Seq(variable, body)
      case PForall(forall, vars, triggers, exp) => Seq(forall) ++ vars ++ triggers ++ Seq(exp)
      case PForPerm(forperm, vars, res, expr) => Seq(forperm) ++ vars ++ Seq(res, expr)
      case PCondExp(cond, q, thn, c, els) => Seq(cond, q, thn, c, els)
      case PInhaleExhaleExp(in, ex) => Seq(in, ex)
      case PCurPerm(loc) => Seq(loc)
      case PNoPerm() => Nil
      case PFullPerm() => Nil
      case PWildcard() => Nil
      case PEpsilon() => Nil
      case PAccPred(acc, loc, perm) => Seq(acc, loc, perm)
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
      case PMacroRef(_) => Nil
      case PEmptyMap(k, v) => Seq(k, v)
      case PExplicitMap(elems) => elems
      case PMapRange(base) => Seq(base)
      case PMapDomain(base) => Seq(base)
      case PMaplet(key, value) => Seq(key, value)
      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
      case PPackageWand(pckg, exp, proofScript) => Seq(pckg, exp, proofScript)
      case PApplyWand(apply, exp) => Seq(apply, exp)
      case PExhale(exhale, exp) => Seq(exhale, exp)
      case PAssert(assert, exp) => Seq(assert, exp)
      case PInhale(inhale, exp) => Seq(inhale, exp)
      case PAssume(assume, exp) => Seq(assume, exp)
      case PRegularNewStmt(target, fields) => Seq(target) ++ fields
      case PStarredNewStmt(target) => Seq(target)
      case PMethodCall(targets, method, args) => targets ++ Seq(method) ++ args
      case PLabel(label, name, invs) => Seq(label, name) ++ invs.flatMap(inv => Seq(inv._1, inv._2))
      case PGoto(label) => Seq(label)
      case PVarAssign(target, rhs) => Seq(target, rhs)
      case PFieldAssign(field, rhs) => Seq(field, rhs)
      case PMacroAssign(call, exp) => Seq(call, exp)
      case PIf(keyword, cond, thn, elsKw, els) => Seq(keyword, cond, thn) ++ elsKw.toSeq ++ Seq(els)
      case PWhile(keyword, cond, invs, body) => Seq(keyword, cond) ++ invs.flatMap(inv => Seq(inv._1, inv._2)) ++ Seq(body)
      case PLocalVarDecl(keyword, idndef, typ, init) => Seq(keyword, idndef, typ) ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PProgram(_, _, domains, fields, functions, predicates, methods, extensions, _) =>
        domains ++ fields ++ functions ++ predicates ++ methods ++ extensions
      case PLocalImport(imprt, _) => Seq(imprt)
      case PStandardImport(imprt, _) => Seq(imprt)
      case PDomain(idndef, typVars, funcs, axioms, _) => Seq(idndef) ++ typVars ++ funcs ++ axioms
      case PField(field, idndef, typ) => Seq(field, idndef, typ)
      case PMethod(idndef, args, rets, pres, posts, body) =>
        Seq(idndef) ++ args ++ rets ++ pres.flatMap(c => Seq(c._1, c._2)) ++ posts.flatMap(c => Seq(c._1, c._2)) ++ body.toSeq
      case PFunction(name, args, typ, pres, posts, body) =>
        Seq(name) ++ args ++ Seq(typ) ++ pres.flatMap(c => Seq(c._1, c._2)) ++ posts.flatMap(c => Seq(c._1, c._2)) ++ body
      case PDomainFunction(name, args, typ, _, _) =>
        Seq(name) ++ args ++ Seq(typ)
      case PPredicate(predicate, name, args, body) =>
        Seq(predicate, name) ++ args ++ body
      case PAxiom(idndef, exp) => (if (idndef.isDefined) Seq(idndef.get) else Nil) ++ Seq(exp)
      case PTypeVarDecl(name) => Seq(name)
      case PDefine(define, idndef, optArgs, body) => Seq(define, idndef) ++ optArgs.getOrElse(Nil) ++ Seq(body)
      case PQuasihavoc(quasihavoc, lhs, e) =>
        Seq(quasihavoc) ++ lhs.toSeq.flatMap(lhs => Seq(lhs._1, lhs._2)) ++ Seq(e)
      case PQuasihavocall(quasihavocall, vars, cc, lhs, e) =>
        Seq(quasihavocall) ++ vars ++ Seq(cc) ++ lhs.toSeq.flatMap(lhs => Seq(lhs._1, lhs._2)) ++ Seq(e)
      case PAnnotatedExp(e, _) => Seq(e)
      case PAnnotatedStmt(s, _) => Seq(s)
      case t: PExtender => t.getSubnodes()
      case _: PSkip => Nil
      case _: PUnnamedFormalArgDecl => Nil
    }
  }
}
