// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.util.concurrent.atomic.{AtomicInteger, AtomicLong}
import viper.silver.ast.utility.Visitor
import viper.silver.ast.utility.lsp._
import viper.silver.ast.utility.rewriter.{Rewritable, StrategyBuilder}
import viper.silver.ast.{Exp, MagicWandOp, Member, NoPosition, Position, Stmt, Type}
import viper.silver.parser.TypeHelper._
import viper.silver.verifier.ParseReport

import scala.collection.Set
import scala.language.implicitConversions
import java.nio.file.Path
import viper.silver.ast.utility.lsp.{HasHoverHints, HoverHint, SelectionBoundTrait}
import viper.silver.ast.utility.lsp.{HasDocumentSymbol, SymbolKind, SymbolTag}
import viper.silver.ast.utility.lsp.{HasSemanticHighlights, SemanticHighlight, TokenType, TokenModifier}

trait Where {
  val pos: (Position, Position)
}

/**
  * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
  * with the actual Viper abstract syntax tree.
  */
trait PNode extends Where with Product with Rewritable with HasDocumentSymbol {

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
        case t: Product =>
          for (v <- t.productIterator)
            setNodeChildConnections(v)
        case _ =>
        // Ignore other kinds of nodes
      }

    _children.clear()
    for (c <- productIterator)
      setNodeChildConnections(c)

  }

  override def getSymbol: Option[DocumentSymbol] = None
  override def getSymbolChildren: Seq[DocumentSymbol] = {
    val getSymbol = { case n => n.getSymbol }: PartialFunction[PNode, Option[DocumentSymbol]]
    val get = { case Some(s) => s }: PartialFunction[Option[DocumentSymbol], DocumentSymbol]
    subnodes flatMap (_ shallowCollect (getSymbol andThen get))
  }
}

object TypeHelper {
  val Int = PPrimitiv(PKeywordType("Int")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Bool = PPrimitiv(PKeywordType("Bool")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Perm = PPrimitiv(PKeywordType("Perm")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Ref = PPrimitiv(PKeywordType("Ref")(NoPosition, NoPosition))((NoPosition, NoPosition))
  val Pred = PPredicateType()((NoPosition, NoPosition))
  val Wand = PWandType()((NoPosition, NoPosition))
  def MakeSet(typ: PType) = PSetType(PKeywordType("Set")(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
  def MakeSeq(typ: PType) = PSeqType(PKeywordType("Seq")(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
  def MakeMap(key: PType, value: PType) = PMapType(PKeywordType("Map")(NoPosition, NoPosition), key, value)((NoPosition, NoPosition))
  def MakeMultiset(typ: PType) = PMultisetType(PKeywordType("Multiset")(NoPosition, NoPosition), typ)((NoPosition, NoPosition))
}

trait PPrettyPrint {
  def pretty(): String
}

// Identifiers (uses and definitions)
trait PIdentifier {
  def name: String
}

case class PIdnDef(name: String)(val pos: (Position, Position)) extends PNode with PIdentifier with PPrettyPrint {
  override def pretty(): String = name
}

case class PIdnUse(name: String)(val pos: (Position, Position))
  extends PExp with PIdentifier with HasSemanticHighlights with HasHoverHints with HasGotoDefinitions {

  var decl: PDeclaration = null
  /* Should be set during resolving. Intended to preserve information
   * that is needed by the translator.
   */
  override val typeSubstitutions = List(PTypeSubstitution.id)

  def forceSubstitution(ts: PTypeSubstitution) = {
    typ = typ.substitute(ts)
    assert(typ.isGround)
  }

  override def prettyNoBrackets = name

  override def getSemanticHighlights: Seq[SemanticHighlight] = (decl, RangePosition(this)) match {
    case (_: PLocalVarDecl, Some(sp)) => Seq(SemanticHighlight(sp, TokenType.Variable))
    case (_: PFormalArgDecl, Some(sp)) => Seq(SemanticHighlight(sp, TokenType.Parameter))
    case _ => Seq()
  }

  override def getHoverHints: Seq[HoverHint] = (decl, RangePosition(this)) match {
    case (decl: PLocalSymbol, Some(sp)) => Seq(HoverHint(decl.finalHint, SelectionBoundScope(sp)))
    case _ => Seq()
  }

  override def getGotoDefinitions: Seq[GotoDefinition] = (decl, RangePosition(this)) match {
    case (decl: PLocalSymbol, Some(sp)) =>
      RangePosition(decl.idndef).map(d => GotoDefinition(d, SelectionBoundScope(sp))).toSeq
    case _ => Seq()
  }
}

trait PKeyword extends PIsSemanticToken with PPrettyPrint {
  def keyword: String
  override def pretty(): String = keyword
}

/** Keywords such a `domain`, `method`, `function`, `predicate`, etc. */
case class PKeywordLang(keyword: String)(val pos: (Position, Position)) extends PKeyword {
  override def tokenType = TokenType.Keyword
}
object PKeywordLang {
  def empty: PKeywordLang = PKeywordLang("")(NoPosition, NoPosition)
}
/** Keywords such a `fold`, `inhale`, `package`, `if`, etc. */
case class PKeywordStmt(keyword: String)(val pos: (Position, Position)) extends PKeyword {
  override def tokenType = TokenType.Keyword
  override def tokenModifier = Seq(TokenModifier.ControlFlow)
}
/** Keywords such a `true`, `false` or `null` */
case class PKeywordConstant(keyword: String)(val pos: (Position, Position)) extends PKeyword {
  override def tokenType = TokenType.Keyword
}
/** Keywords such a `Int`, `Ref`, `Set`, `Map`, etc. */
case class PKeywordType(keyword: String)(val pos: (Position, Position)) extends PKeyword {
  override def tokenType = TokenType.Type
}

trait POperator extends PIsSemanticToken {
  def operator: String
}

/** Keywords such a `union`, `in`, `intersect`, `acc`, etc. */
case class PKeywordOperator(keyword: String)(val pos: (Position, Position)) extends PKeyword with POperator {
  override def tokenType = TokenType.Keyword
  override def operator = keyword
}
/** Operators such a `--*`, `==`, `<=`, `-`, etc. */
case class POperatorSymbol(operator: String)(val pos: (Position, Position)) extends POperator {
  override def tokenType = TokenType.Operator
}

trait PAnyFormalArgDecl extends PNode with PUnnamedTypedDeclaration with PPrettyPrint

case class PUnnamedFormalArgDecl(var typ: PType)(val pos: (Position, Position)) extends PAnyFormalArgDecl {
  override def pretty(): String = typ.pretty()
}

/* Formal arguments.
 * [2014-11-13 Malte] Changed type to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PFormalArgDecl(idndef: PIdnDef, var typ: PType)(val pos: (Position, Position))
  extends PAnyFormalArgDecl with PTypedDeclaration with PLocalDeclaration with PSemanticDeclaration with PLocalSymbol {

  override def pretty(): String = s"${idndef.pretty()}: ${typ.pretty()}"
  override def tokenType = TokenType.Parameter
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Variable
  override def hint: String = pretty()
  override def detail: Option[String] = Some(typ.pretty())
}

// Types
trait PType extends PNode with PPrettyPrint {
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


case class PPrimitiv(name: PKeywordType)(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PType {
  override def substitute(ts: PTypeSubstitution): PType = this

  override val subNodes = Seq()

  override def pretty() = name.pretty()

  override def isValidOrUndeclared = true
}

case class PDomainType(domain: PIdnUse, args: Seq[PType])(val pos: (Position, Position)) extends PGenericType with HasSemanticHighlights {
  val genericName = domain.name
  override val typeArguments = args //if (kind==PDomainTypeKinds.Domain)
  var kind: PDomainTypeKinds.Kind = PDomainTypeKinds.Unresolved
  override val subNodes = args

  /* This class is also used to represent type variables, as they cannot
   * be distinguished syntactically from domain types without generic arguments.
   * For type variables, we have args.length = 0
   */
  def isTypeVar = kind == PDomainTypeKinds.TypeVar

  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(domain).flatMap(sp => kind match {
    case PDomainTypeKinds.TypeVar => Some(SemanticHighlight(sp, TokenType.TypeParameter))
    case PDomainTypeKinds.Domain => Some(SemanticHighlight(sp, TokenType.Interface))
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

  override def pretty() = domain.pretty() + (if (args.isEmpty) "" else s"[${args.map(_.pretty()).mkString(", ")}]")
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

  override def pretty() = s"$genericName[${typeArguments.mkString(", ")}]"

  def withTypeArguments(s: Seq[PType]): PGenericType
}

sealed trait PGenericCollectionType extends PGenericType {
  def elementType: PType

  override val typeArguments = Seq(elementType)
  override val subNodes = Seq(elementType)

  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)
}

case class PSeqType(seq: PKeywordType, elementType: PType)(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Seq"

  override def substitute(map: PTypeSubstitution) = PSeqType(seq, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PSetType(set: PKeywordType, elementType: PType)(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Set"

  override def substitute(map: PTypeSubstitution) = PSetType(set, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]) = copy(elementType = s.head)(pos)
}

case class PMultisetType(multiset: PKeywordType, elementType: PType)(val pos: (Position, Position)) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"

  override def substitute(map: PTypeSubstitution) = PMultisetType(multiset, elementType.substitute(map))(pos)

  override def withTypeArguments(s: Seq[PType]): PMultisetType = copy(elementType = s.head)(pos)
}

case class PMapType(map: PKeywordType, keyType: PType, valueType: PType)(val pos: (Position, Position)) extends PType with PGenericType {
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
  override def pretty() = "<error type>"

  override def isValidOrUndeclared = false
}

// used during resolving for predicate accesses
case class PPredicateType()(val pos: (Position, Position) = (NoPosition, NoPosition)) extends PInternalType {
  override def pretty() = "$predicate"

  override def isValidOrUndeclared = true
}

case class PWandType()(val pos: (Position, Position)) extends PInternalType {
  override def pretty() = "$wand"

  override def isValidOrUndeclared = true
}

///////////////////////////////////////////////////////////////////////////////////////
// Expressions
// typeSubstitutions are the possible substitutions used for type checking and inference
// The argument types are unified with the (fresh versions of) types  are
trait PExp extends PNode with PPrettyPrint {
  var bracketed: Boolean = false
  var typ: PType = PUnknown()()

  def typeSubstitutions: scala.collection.Seq[PTypeSubstitution]

  def forceSubstitution(ts: PTypeSubstitution): Unit

  def prettyNoBrackets: String
  override def pretty(): String = if (bracketed) s"($prettyNoBrackets)" else prettyNoBrackets
}

case class PAnnotatedExp(e: PExp, annotation: PAnnotation)(val pos: (Position, Position)) extends PExp {
  override def typeSubstitutions: collection.Seq[PTypeSubstitution] = e.typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution): Unit = e.forceSubstitution(ts)
  override def prettyNoBrackets = e.pretty()
}

case class PMagicWandExp(override val left: PExp, wand: POperatorSymbol, override val right: PExp)(val posi: (Position, Position)) extends PBinExp(left, wand, right)(posi) with PResourceAccess

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

trait PAnyCall extends POpApp {
  val typeAnnotated: Option[PType]

  override def prettyNoBrackets = {
    val call = s"$opName(${args.map(_.pretty()).mkString(", ")})"
    typeAnnotated match {
      case None => call
      case Some(tp) => s"($call: ${tp.pretty()})"
    }
  }
}

trait POpAppKeyword extends POpApp {
  def op: POperator
  override def opName = op.operator
}

case class PCall(func: PIdnUse, args: Seq[PExp], typeAnnotated: Option[PType] = None)(val pos: (Position, Position))
  extends PAnyCall with PLocationAccess with HasSemanticHighlights with HasInlayHints {
  override val idnuse = func
  override val opName = func.name

  override def getSemanticHighlights: Seq[SemanticHighlight] = (RangePosition(func), function, extfunction, method) match {
    case (_, null, null, null) => Seq()
    case (Some(sp), _: PDomainFunction, null, null) => Seq(SemanticHighlight(sp, TokenType.Function))
    case (Some(sp), _: PFunction, null, null) => Seq(SemanticHighlight(sp, TokenType.Function))
    case (Some(sp), null, _, null) => Seq(SemanticHighlight(sp, TokenType.Struct))
    case (Some(sp), null, null, _) => Seq(SemanticHighlight(sp, TokenType.Method))
    case _ => Seq()
  }
  def getFormalArgs: Seq[PAnyFormalArgDecl] = (function, extfunction, method) match {
    case (null, null, null) => Seq()
    case (function, null, null) => function.formalArgs
    case (null, predicate, null) => predicate.formalArgs
    case (null, null, method) => method.formalArgs
    case _ => Seq()
  }
  def idnUseMatchesArg(decl: String, use: String): Boolean = {
    val d = decl.toLowerCase()
    val parts = use.toLowerCase().split('_')
    parts.head == d || parts.last == d
  }
  override def getInlayHints: Seq[InlayHint] = getFormalArgs.zip(args).flatMap {
    case (_: PUnnamedFormalArgDecl, _) => None
    case (PFormalArgDecl(decl, _), PIdnUse(use)) if idnUseMatchesArg(decl.name, use) => None
    case (PFormalArgDecl(decl, _), arg) => (RangePosition(decl), RangePosition(arg)) match {
      case (Some(declRp), Some(argRp)) => {
        val declName = InlayHintLabelPart(decl.pretty(), None, Some(declRp))
        val label = Seq(declName, InlayHintLabelPart(":"))
        Some(InlayHint(argRp, label, Some(InlayHintKind.Parameter), false, true))
      }
      case _ => None
    }
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
  // TODO: get rid of this duplication, where a method call is parsed as
  // a PCall! E.g. by removing the `PMethodCall` node
  var method: PMethod = null

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

case class PTrigger(exp: Seq[PExp])(val pos: (Position, Position)) extends PNode with PPrettyPrint {
  override def pretty() = s"{ ${exp.map(_.pretty()).mkString(", ")} }"
}

class PBinExp(val left: PExp, val op: POperator, val right: PExp)(val pos: (Position, Position)) extends POpAppKeyword {

  override val args = Seq(left, right)
  override def prettyNoBrackets = s"${left.pretty()} ${op.operator} ${right.pretty()}"
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
  override def prettyNoBrackets = s"${op.operator}${exp.pretty()}"
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

case class PCondExp(cond: PExp, q: POperatorSymbol, thn: PExp, c: POperatorSymbol, els: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "?:"
  override val args = Seq(cond, thn, els)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool, POpApp.pArgS(2) -> POpApp.pArg(1), POpApp.pResS -> POpApp.pArg(1))
  )
  override def prettyNoBrackets = s"${cond.pretty()} ${q.operator} ${thn.pretty()} ${c.operator} ${els.pretty()}"
}

// Simple literals
sealed trait PSimpleLiteral extends PExp {
  override final val typeSubstitutions = Seq(PTypeSubstitution.id)

  def forceSubstitution(ts: PTypeSubstitution) = {}
}

sealed trait PConstantLiteral extends PSimpleLiteral {
  val keyword: PKeywordConstant
  override def prettyNoBrackets = keyword.pretty()
}

case class PIntLit(i: BigInt)(val pos: (Position, Position)) extends PSimpleLiteral {
  typ = Int
  override def prettyNoBrackets = i.toString()
}

case class PResultLit(result: PKeywordLang)(val pos: (Position, Position)) extends PSimpleLiteral {
  override def prettyNoBrackets = result.pretty()
}

case class PBoolLit(keyword: PKeywordConstant, b: Boolean)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Bool
}

case class PNullLit(keyword: PKeywordConstant)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Ref
}

sealed trait PHeapOpApp extends POpApp

sealed trait PResourceAccess extends PHeapOpApp

trait PLocationAccess extends PResourceAccess {
  def idnuse: PIdnUse
}

case class PFieldAccess(rcv: PExp, idnuse: PIdnUse)(val pos: (Position, Position)) extends PLocationAccess with HasSemanticHighlights {
  override final val opName = "."
  override final val args = Seq(rcv)

  override def prettyNoBrackets = s"${rcv.pretty()}.${idnuse.pretty()}"

  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(idnuse).map(sp => SemanticHighlight(sp, TokenType.Property)).toSeq

  override def signatures =
    if (Set(rcv.typ, idnuse.typ).forall(_.isValidOrUndeclared))
      List(PTypeSubstitution(Map(POpApp.pArgS(0) -> Ref, POpApp.pResS -> idnuse.typ)))
    else
      List()
  //setType()
}

// case class PPredicateAccess(args: Seq[PExp], idnuse: PIdnUse)(val pos: (Position, Position)) extends PLocationAccess {
//   override final val opName = "acc"
//   var predicate: PPredicate = null

//   override def signatures = if (predicate == null) List() else
//     List(new PTypeSubstitution(
//       args.indices.map(i => POpApp.pArg(i).domain.name -> predicate.formalArgs(i).typ) :+
//         (POpApp.pRes.domain.name -> Pred)))
// }

case class PUnfolding(op: PKeywordOperator, acc: PAccPred, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp with POpAppKeyword {
  override val args = Seq(acc, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> POpApp.pArg(1)))
  override def prettyNoBrackets = s"${op.pretty()} ${acc.pretty()} in ${exp.pretty()}"
}

case class PApplying(op: PKeywordOperator, wand: PExp, exp: PExp)(val pos: (Position, Position)) extends PHeapOpApp with POpAppKeyword {
  override val args = Seq(wand, exp)
  override val signatures: List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Wand, POpApp.pResS -> POpApp.pArg(1)))
  override def prettyNoBrackets = s"${op.pretty()} (${wand.pretty()}) in ${exp.pretty()}"
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
  def keyword: PKeywordLang

  def vars: Seq[PFormalArgDecl]

  def triggers: Seq[PTrigger]

  override def prettyNoBrackets = {
    val varsStr = vars.map(_.pretty()).mkString(", ")
    val triggersStr = triggers.map(_.pretty() + " ").mkString
    s"${keyword.pretty()} $varsStr :: $triggersStr${body.pretty()}"
  }
}

case class PExists(keyword: PKeywordLang, vars: Seq[PFormalArgDecl], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForall(keyword: PKeywordLang, vars: Seq[PFormalArgDecl], triggers: Seq[PTrigger], body: PExp)(val pos: (Position, Position)) extends PQuantifier

case class PForPerm(keyword: PKeywordLang, vars: Seq[PFormalArgDecl], accessRes: PResourceAccess, body: PExp)(val pos: (Position, Position)) extends PQuantifier {
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

  override def prettyNoBrackets = s"let ${nestedScope.variable.pretty()} == (${exp.pretty()}) in ${body.pretty()}"

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
  override def prettyNoBrackets = s"[${in.pretty()}, ${ex.pretty()}]"
}

case class PCurPerm(res: PResourceAccess)(val pos: (Position, Position)) extends PHeapOpApp {
  override val opName = "#perm"
  override val args = Seq(res)
  val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> Perm)
  )
  override def prettyNoBrackets = s"perm(${res.pretty()})"
}

case class PNoPerm(keyword: PKeywordConstant)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PFullPerm(keyword: PKeywordConstant)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}
object PFullPerm {
  def implied(): PFullPerm = PFullPerm(PKeywordConstant("full")(NoPosition, NoPosition))(NoPosition, NoPosition)
}

case class PWildcard(keyword: PKeywordConstant)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PEpsilon(keyword: PKeywordConstant)(val pos: (Position, Position)) extends PConstantLiteral {
  typ = Perm
}

case class PAccPred(op: PKeywordOperator, loc: PLocationAccess, perm: PExp)(val pos: (Position, Position)) extends POpAppKeyword {
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(1) -> Perm, POpApp.pResS -> Bool))
  override val args = Seq(loc, perm)
  override def prettyNoBrackets = s"${op.pretty()}(${loc.pretty()}, ${perm.pretty()})"
}

sealed trait POldExp extends PHeapOpApp {
  def e: PExp

  override val args = Seq(e)
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> POpApp.pArg(0)))
}

case class POld(e: PExp)(val pos: (Position, Position)) extends POldExp {
  override val opName = "old"
  override def prettyNoBrackets = s"old(${e.pretty()})"
}

case class PLabelledOld(label: PIdnUse, e: PExp)(val pos: (Position, Position)) extends POldExp with HasSemanticHighlights {
  override val opName = "old#labeled"
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(label).map(sp => SemanticHighlight(sp, TokenType.Event)).toSeq
  override def prettyNoBrackets = s"old[${label.pretty()}](${e.pretty()})"
}

sealed trait PCollectionLiteral extends POpApp {
  def pElementType: PType

  def pCollectionType(pType: PType): PType

  def collectionName: String
  def explicitType: Option[PType]

  override def prettyNoBrackets = {
    val tp = explicitType.map(tp => s"[${tp.pretty()}]").getOrElse("")
    s"$collectionName$tp(${args.map(_.pretty()).mkString(", ")})"
  }
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
  override val opName = "Seq#Seq"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSeq(pType)
  override def collectionName: String = "Seq"
}

case class PEmptySeq(pElementType: PType)(val pos: (Position, Position)) extends PSeqLiteral with PEmptyCollectionLiteral

case class PExplicitSeq(override val args: Seq[PExp])(val pos: (Position, Position)) extends PSeqLiteral with PExplicitCollectionLiteral

case class PRangeSeq(low: PExp, high: PExp)(val pos: (Position, Position)) extends POpApp {
  override val opName = "Seq#RangeSeq"
  override val args = Seq(low, high)
  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Int, POpApp.pArgS(1) -> Int, POpApp.pResS -> MakeSeq(Int)))

  override def prettyNoBrackets = s"[${low.pretty()}..${high.pretty()}]"
}

// case class PSeqIndex(seq: PExp, idx: PExp)(val pos: (Position, Position)) extends POpApp {
//   override val opName = "Seq#At"
//   override val args = Seq(seq, idx)
//   override val signatures: List[PTypeSubstitution] = List(
//     Map(
//       POpApp.pArgS(0) -> MakeSeq(POpApp.pRes),
//       POpApp.pArgS(1) -> Int)
//   )

//   override def prettyNoBrackets = s"${seq.pretty()}[${idx.pretty()}]"
// }

case class PLookup(base: PExp, idx: PExp)(val pos: (Position, Position)) extends POpApp {
  val keyType: PDomainType = POpApp.pArg(1)

  override val opName = "lookup"
  override val args = Seq(base, idx)
  override val extraLocalTypeVariables: Set[PDomainType] = Set(keyType)

  override val signatures: List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> MakeSeq(POpApp.pRes), POpApp.pArgS(1) -> Int),
    Map(POpApp.pArgS(0) -> MakeMap(keyType, POpApp.pRes))
  )

  override def prettyNoBrackets = s"${base.pretty()}[${idx.pretty()}]"
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

  override def prettyNoBrackets = s"${seq.pretty()}[..${n.pretty()}]"
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

  override def prettyNoBrackets = s"${seq.pretty()}[${n.pretty()}..]"
}

// case class PSeqUpdate(seq: PExp, idx: PExp, elem: PExp)(val pos: (Position, Position)) extends POpApp {
//   override val opName = "Seq#update"
//   val elementType = POpApp.pArg(2)
//   override val args = Seq(seq, idx, elem)
//   override val signatures: List[PTypeSubstitution] = List(
//     Map(
//       POpApp.pArgS(0) -> MakeSeq(elementType),
//       POpApp.pArgS(1) -> Int,
//       POpApp.pResS -> MakeSeq(elementType)
//     ))
//   override val extraLocalTypeVariables = Set(elementType)
// }

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

  override def prettyNoBrackets = s"${base.pretty()}[${key.pretty()} := ${value.pretty()}]"
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

  override def prettyNoBrackets = s"|${seq.pretty()}|"
}

sealed trait PSetLiteral extends PCollectionLiteral {
  override val opName = "Set#Set"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeSet(pType)

  def collectionName: String = "Set"
}

case class PEmptySet(pElementType: PType)(val pos: (Position, Position)) extends PSetLiteral with PEmptyCollectionLiteral

case class PExplicitSet(args: Seq[PExp])(val pos: (Position, Position)) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral {
  override val opName = "Multiset#Multiset"

  def pCollectionType(pType: PType) = if (pType.isUnknown) PUnknown()() else MakeMultiset(pType)

  def collectionName: String = "Multiset"
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

  def explicitType: Option[(PType, PType)] = (pKeyType, pValueType) match {
      case (PTypeVar("#K"), PTypeVar("#E")) => None
      case (key, value) => Some((key, value))
    }
  override def prettyNoBrackets = {
    val tp = explicitType.map(tp => s"[${tp._1.pretty()}, ${tp._2.pretty()}]").getOrElse("")
    s"Map$tp()"
  }
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

  override def prettyNoBrackets = s"Map(${args.map(_.pretty()).mkString(", ")})"
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

  override def prettyNoBrackets = s"${key.pretty()} := ${value.pretty()}"
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

  override def prettyNoBrackets = s"domain(${base.pretty()})"
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

  override def prettyNoBrackets = s"domain(${base.pretty()})"
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

case class PAnnotatedStmt(stmt: PStmt, annotation: PAnnotation)(val pos: (Position, Position)) extends PStmt

case class PSeqn(ss: Seq[PStmt])(val pos: (Position, Position)) extends PStmt with PScope

case class PFold(fold: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PUnfold(unfold: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PPackageWand(pckg: PKeywordStmt, wand: PExp, proofScript: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PApplyWand(apply: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PExhale(exhale: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssert(assert: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PAssume(assume: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PInhale(inhale: PKeywordStmt, e: PExp)(val pos: (Position, Position)) extends PStmt

case class PVarAssign(idnuse: PIdnUse, rhs: PExp)(val pos: (Position, Position)) extends PStmt

case class PFieldAssign(fieldAcc: PFieldAccess, rhs: PExp)(val pos: (Position, Position)) extends PStmt

case class PMacroAssign(call: PCall, exp: PExp)(val pos: (Position, Position)) extends PStmt

case class PIf(keyword: PKeywordStmt, cond: PExp, thn: PSeqn, elsKw: Option[PKeywordStmt], els: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PWhile(keyword: PKeywordStmt, cond: PExp, invs: Seq[(PKeywordLang, PExp)], body: PSeqn)(val pos: (Position, Position)) extends PStmt

case class PLocalVarDecl(keyword: PKeywordStmt, idndef: PIdnDef, typ: PType, init: Option[PExp])(val pos: (Position, Position))
  extends PStmt with PTypedDeclaration with PLocalDeclaration with PSemanticDeclaration with PLocalSymbol {

  override def tokenType = TokenType.Variable
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Variable
  override def hint: String = s"${keyword.pretty()} ${idndef.pretty()}: ${typ.pretty()}"
  override def detail: Option[String] = Some(typ.pretty())
}

case class PGlobalVarDecl(idndef: PIdnDef, typ: PType)(val pos: (Position, Position)) extends PTypedDeclaration with PUniversalDeclaration

case class PMethodCall(targets: Seq[PIdnUse], method: PIdnUse, args: Seq[PExp])(val pos: (Position, Position)) extends PStmt with HasSemanticHighlights with HasInlayHints {
  
  var resolved: PMethod = null

  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(method).map(SemanticHighlight(_, TokenType.Method)).toSeq

  def getFormalArgs: Seq[PFormalArgDecl] = if (resolved == null) Seq() else resolved.formalArgs
  // TODO: remove duplication with `PCall`
  def idnUseMatchesArg(decl: String, use: String): Boolean = {
    val d = decl.toLowerCase()
    val parts = use.toLowerCase().split('_')
    parts.head == d || parts.last == d
  }
  override def getInlayHints: Seq[InlayHint] = getFormalArgs.zip(args).flatMap {
    case (PFormalArgDecl(decl, _), PIdnUse(use)) if idnUseMatchesArg(decl.name, use) => None
    case (PFormalArgDecl(decl, _), arg) => (RangePosition(decl), RangePosition(arg)) match {
      case (Some(declRp), Some(argRp)) => {
        val declName = InlayHintLabelPart(decl.pretty(), None, Some(declRp))
        val label = Seq(declName, InlayHintLabelPart(":"))
        Some(InlayHint(argRp, label, Some(InlayHintKind.Parameter), false, true))
      }
      case _ => None
    }
  }
}

case class PLabel(label: PKeywordStmt, idndef: PIdnDef, invs: Seq[(PKeywordLang, PExp)])(val pos: (Position, Position))
  extends PStmt with PLocalDeclaration with PSemanticDeclaration with PLocalSymbol {

  override def tokenType = TokenType.Event
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Event
  override def hint: String = {
    val firstLine = s"${label.pretty()} ${idndef.pretty()}"
    val invsStr = invs.map(i => s"\n  ${i._1.pretty()} ${i._2.pretty()}").mkString
    firstLine + invsStr
  }
}

case class PGoto(goto: PKeywordStmt, targets: PIdnUse)(val pos: (Position, Position)) extends PStmt with HasSemanticHighlights {
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(targets).map(sp => SemanticHighlight(sp, TokenType.Event)).toSeq
}

case class PTypeVarDecl(idndef: PIdnDef)(val pos: (Position, Position)) extends PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.TypeParameter
}

case class PMacroRef(idnuse: PIdnUse)(val pos: (Position, Position)) extends PStmt

case class PDefine(define: PKeywordLang, idndef: PIdnDef, parameters: Option[Seq[PIdnDef]], body: PNode)(val pos: (Position, Position)) extends PStmt with PLocalDeclaration with PSemanticDeclaration {
  override def tokenType = TokenType.Macro
}

case class PSkip()(val pos: (Position, Position)) extends PStmt

case class PQuasihavoc(quasihavoc: PKeywordStmt, lhs: Option[(PExp, POperatorSymbol)], e: PExp)(val pos: (Position, Position)) extends PStmt

case class PQuasihavocall(quasihavocall: PKeywordStmt, vars: Seq[PFormalArgDecl], colons: POperatorSymbol, lhs: Option[(PExp, POperatorSymbol)], e: PExp)(val pos: (Position, Position)) extends PStmt with PScope

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

// Annotations
trait PAnnotated extends PNode {
  val annotations: Seq[PAnnotation]
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

trait PGlobalDeclaration extends PDeclaration with PAnnotated

trait PLocalDeclaration extends PDeclaration

trait PUniversalDeclaration extends PDeclaration

sealed trait PTypedDeclaration extends PDeclaration with PUnnamedTypedDeclaration

trait PSemanticDeclaration extends PDeclaration with HasSemanticHighlights {
  def tokenType: TokenType.TokenType
  def tokenModifier: Seq[TokenModifier.TokenModifier] = Seq()
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(idndef).map(sp => SemanticHighlight(sp, tokenType, tokenModifier)).toSeq
}

trait PIsSemanticToken extends PNode with HasSemanticHighlights {
  def tokenType: TokenType.TokenType
  def tokenModifier: Seq[TokenModifier.TokenModifier] = Seq()
  override def getSemanticHighlights: Seq[SemanticHighlight] = RangePosition(this).map(sp => SemanticHighlight(sp, tokenType, tokenModifier)).toSeq
}

// trait PGlobalSymbol extends PGlobalDeclaration with DefinesSymbols {
//   def hint: () => String
//   def scope: Option[SourcePosition] = None
//   def kind: SymbolKind.SymbolKind
//   def detail: Option[String] = None
//   def isDeprecated: Boolean = false
//   override def symbolDefns: Seq[CanGotoDefinition] = (idndef.sourcePos, sourcePos) match {
//     case (Some(selectionRange), Some(range)) => 
//       Seq(GotoDefinition(hint, idndef.name, selectionRange, range, kind, scope, detail, if (isDeprecated) Seq(SymbolTag.Deprecated) else Seq()))
//     case _ => Seq()
//   }
// }


trait PDeclarationSymbol extends PDeclaration with HasDocumentSymbol {
  def symbolKind: SymbolKind.SymbolKind
  def detail: Option[String] = None
  def isDeprecated: Boolean = false
  def imports: Option[Path] = None
  def tags: Seq[SymbolTag.SymbolTag] = if (isDeprecated) Seq(SymbolTag.Deprecated) else Seq()

  override def getSymbol: Option[DocumentSymbol] = (RangePosition(this), RangePosition(idndef)) match {
    case (Some(range), Some(selectionRange)) => Some(DocumentSymbol(idndef.pretty(), detail, range, selectionRange, symbolKind, tags, None, getSymbolChildren))
    case _ => None
  }
}

trait PGlobalSymbol extends PGlobalDeclaration with PDeclarationSymbol with HasHoverHints with HasGotoDefinitions {
  def hint: String
  def finalHint: String = {
    val documentation = annotations.filter(_.key == "doc").map(_.values.mkString("\n")).mkString("\n---\n")
    s"```\n$hint\n```\n$documentation"
  }
  def scope: SelectionBoundTrait = SelectionBoundKeyword(idndef.name)
  override def getHoverHints: Seq[HoverHint] = Seq(HoverHint(finalHint, scope))
  override def getGotoDefinitions: Seq[GotoDefinition] = RangePosition(idndef).map(rp => GotoDefinition(rp, scope)).toSeq
}

trait PGlobalCallable extends PGlobalSymbol with HasFoldingRanges with HasSignatureHelps {
  def keyword: PKeywordLang
  def bodyRange: Option[RangePosition]
  def formalArgs: Seq[PAnyFormalArgDecl]
  def returnString: Option[String]
  def pres: Seq[(PKeywordLang, PExp)]
  def posts: Seq[(PKeywordLang, PExp)]
  override def hint: String = {
    val firstLine = s"${keyword.pretty()} ${idndef.pretty()}(${formalArgs.map(_.pretty()).mkString(", ")})${returnString.getOrElse("")}"
    val contract = (pres ++ posts).map(p => s"\n  ${p._1.pretty()} ${p._2.pretty()}")
    val bodyString = bodyRange.map(_ => if (contract.length > 0) "\n{ ... }" else " { ... }").getOrElse("")
    s"$firstLine${contract.mkString}$bodyString"
  }
  override def getSignatureHelps: Seq[SignatureHelp] = ???
  override def getFoldingRanges: Seq[FoldingRange] = {
    val thisRange = RangePosition(this).filter(rp => rp.start.line != rp._end.line)
    val bodyRangeFilter = bodyRange.filter(rp => rp.start.line != rp._end.line)
    val sameStart = thisRange.zip(bodyRangeFilter).map(rps => rps._1.start.line == rps._2.start.line).getOrElse(false)
    val ranges = if (sameStart) thisRange.toSeq else (thisRange.toSeq ++ bodyRangeFilter.toSeq)
    ranges.map(FoldingRange(_))
  }
}

trait PLocalSymbol extends PLocalDeclaration with PDeclarationSymbol with HasHoverHints with HasGotoDefinitions {
  def hint: String
  def finalHint: String = s"```\n$hint\n```"
  // TODO: should this be `RangePosition(this)` or `RangePosition(idndef)`?
  def scope: Option[(RangePosition, SelectionBoundTrait)] = RangePosition(idndef).map(rp => (rp, SelectionBoundScope(rp)))
  override def getHoverHints: Seq[HoverHint] = scope.map(scope => HoverHint(finalHint, scope._2)).toSeq
  override def getGotoDefinitions: Seq[GotoDefinition] = scope.map(scope => GotoDefinition(scope._1, scope._2)).toSeq
}

abstract class PErrorEntity extends PEntity {
  def name: String
}


// a member (like method or axiom) that is its own name scope
trait PMember extends PDeclaration with PScope

trait PAnyFunction extends PMember with PGlobalDeclaration with PTypedDeclaration with PSemanticDeclaration with PGlobalCallable {
  def formalArgs: Seq[PAnyFormalArgDecl]
  override def tokenType = TokenType.Function
  override def symbolKind = SymbolKind.Function
  override def returnString: Option[String] = Some(s": ${typ.pretty()}")
  // override def getGotoDefinitions: Seq[GotoDefinition] = super.getGotoDefinitions ++ formalArgs.map(_.getGotoDefinitions)
}

case class PProgram(imports: Seq[PImport], macros: Seq[PDefine], domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod], extensions: Seq[PExtender], errors: Seq[ParseReport])(val pos: (Position, Position))
  extends PNode with HasSemanticHighlights with HasGotoDefinitions with HasHoverHints with HasFoldingRanges with HasInlayHints with HasCodeLens with HasSignatureHelps {

  override def getSemanticHighlights: Seq[SemanticHighlight] = subnodes.flatMap(_ deepCollect { case sn: HasSemanticHighlights => sn.getSemanticHighlights }).flatten
  override def getGotoDefinitions: Seq[GotoDefinition] = subnodes.flatMap(_ deepCollect { case sn: HasGotoDefinitions => sn.getGotoDefinitions }).flatten
  override def getHoverHints: Seq[HoverHint] = subnodes.flatMap(_ deepCollect { case sn: HasHoverHints => sn.getHoverHints }).flatten
  override def getFoldingRanges: Seq[FoldingRange] = subnodes.flatMap(_ deepCollect { case sn: HasFoldingRanges => sn.getFoldingRanges }).flatten
  override def getInlayHints: Seq[InlayHint] = subnodes.flatMap(_ deepCollect { case sn: HasInlayHints => sn.getInlayHints }).flatten
  override def getCodeLens: Seq[CodeLens] = subnodes.flatMap(_ deepCollect { case sn: HasCodeLens => sn.getCodeLens }).flatten
  override def getSignatureHelps: Seq[SignatureHelp] = subnodes.flatMap(_ deepCollect { case sn: HasSignatureHelps => sn.getSignatureHelps }).flatten
}

abstract class PImport() extends PNode with Where {
  var resolved: Path = null
  override def getSymbol: Option[DocumentSymbol] = RangePosition(this) match {
    case Some(rp) if resolved != null =>
      // We avoid any circular dependencies since `resolved` is only set for imports which caused a
      // file to actually be imported.
      Some(DocumentSymbol(resolved.getFileName.toString(), None, rp, rp, SymbolKind.File, Seq(), Some(resolved)))
    case _ => None
  }
}

case class PLocalImport(imprt: PKeywordLang, file: String)(val pos: (Position, Position)) extends PImport()

case class PStandardImport(imprt: PKeywordLang, file: String)(val pos: (Position, Position)) extends PImport()

case class PMethod(annotations: Seq[PAnnotation], method: PKeywordLang, idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[(PKeywordLang, PExp)], posts: Seq[(PKeywordLang, PExp)], body: Option[PSeqn])
                  (val pos: (Position, Position)) extends PMember with PGlobalDeclaration with PSemanticDeclaration with PGlobalCallable {

  def deepCopy(annotations: Seq[PAnnotation] = this.annotations, method: PKeywordLang = this.method, idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, formalReturns: Seq[PFormalArgDecl] = this.formalReturns, pres: Seq[(PKeywordLang, PExp)] = this.pres, posts: Seq[(PKeywordLang, PExp)] = this.posts, body: Option[PSeqn] = this.body): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(annotations, method, idndef, formalArgs, formalReturns, pres, posts, body)(p.pos)
    }).execute[PMethod](this)
  }

  def deepCopyWithNameSubstitution(annotations: Seq[PAnnotation] = this.annotations, method: PKeywordLang = this.method, idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, formalReturns: Seq[PFormalArgDecl] = this.formalReturns, pres: Seq[(PKeywordLang, PExp)] = this.pres, posts: Seq[(PKeywordLang, PExp)] = this.posts, body: Option[PSeqn] = this.body)
                                  (idn_generic_name: String, idn_substitution: String): PMethod = {
    StrategyBuilder.Slim[PNode]({
      case p: PMethod => PMethod(annotations, method, idndef, formalArgs, formalReturns, pres, posts, body)(p.pos)
      case p@PIdnDef(name) if name == idn_generic_name => PIdnDef(idn_substitution)(p.pos)
      case p@PIdnUse(name) if name == idn_generic_name => PIdnUse(idn_substitution)(p.pos)
    }).execute[PMethod](this)
  }

  override def keyword: PKeywordLang = method
  override def tokenType = TokenType.Method
  override def symbolKind = SymbolKind.Method
  override def returnString: Option[String] = Some(s" returns (${formalReturns.map(_.hint).mkString(", ")})")
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
}

case class PDomain(annotations: Seq[PAnnotation], domain: PKeywordLang, idndef: PIdnDef, typVars: Seq[PTypeVarDecl], members: PDomainMembers, interpretations: Option[Map[String, String]])
                  (val pos: (Position, Position)) extends PMember with PGlobalDeclaration with PSemanticDeclaration with PGlobalSymbol with HasFoldingRanges {
  override def tokenType = TokenType.Interface
  override def symbolKind = SymbolKind.Interface
  override def hint = {
    val tvsStr = if (typVars.isEmpty) "" else typVars.map(_.idndef.pretty()).mkString("[", ",", "]")
    s"${domain.pretty()} ${idndef.pretty()}$tvsStr"
  }
  override def getFoldingRanges: Seq[FoldingRange] = RangePosition(members).map(FoldingRange(_)).toSeq
}
case class PFunction(annotations: Seq[PAnnotation], function: PKeywordLang, idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[(PKeywordLang, PExp)], posts: Seq[(PKeywordLang, PExp)], body: Option[PBlock[PExp]])
                    (val pos: (Position, Position)) extends PAnyFunction with HasFoldingRanges {
  def deepCopy(annotations: Seq[PAnnotation] = this.annotations, function: PKeywordLang = this.function, idndef: PIdnDef = this.idndef, formalArgs: Seq[PFormalArgDecl] = this.formalArgs, typ: PType = this.typ, pres: Seq[(PKeywordLang, PExp)] = this.pres, posts: Seq[(PKeywordLang, PExp)] = this.posts, body: Option[PBlock[PExp]] = this.body): PFunction = {
    StrategyBuilder.Slim[PNode]({
      case p: PFunction => PFunction(annotations, function, idndef, formalArgs, typ, pres, posts, body)(p.pos)
    }).execute[PFunction](this)
  }

  override def keyword: PKeywordLang = function
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
}

case class PDomainFunction(annotations: Seq[PAnnotation], function: PKeywordLang, idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl], typ: PType, unique: Boolean, interpretation: Option[String])
                          (val domainName:PIdnUse)(val pos: (Position, Position)) extends PAnyFunction {

  override def keyword: PKeywordLang = function
  override def pres: Seq[(PKeywordLang, PExp)] = Seq()
  override def posts: Seq[(PKeywordLang, PExp)] = Seq()
  override def bodyRange: Option[RangePosition] = None
}
case class PAxiom(annotations: Seq[PAnnotation], axiom: PKeywordLang, idndef: Option[PIdnDef], exp: PBlock[PExp])(val domainName:PIdnUse)(val pos: (Position, Position)) extends PScope with HasFoldingRanges {

  override def getFoldingRanges: Seq[FoldingRange] = RangePosition(exp).map(FoldingRange(_)).toSeq
}
case class PDomainMembers(funcs: Seq[PDomainFunction], axioms: Seq[PAxiom])(val pos: (Position, Position)) extends PNode
case class PField(annotations: Seq[PAnnotation], field: PKeywordLang, idndef: PIdnDef, typ: PType)(val pos: (Position, Position))
  extends PMember with PTypedDeclaration with PGlobalDeclaration with PSemanticDeclaration with PGlobalSymbol {

  override def tokenType = TokenType.Property
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Property
  override def hint: String = s"${field.pretty()} ${idndef.pretty()}: ${typ.pretty()}"
  override def detail: Option[String] = Some(typ.pretty())
}
case class PPredicate(annotations: Seq[PAnnotation], predicate: PKeywordLang, idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: Option[PBlock[PExp]])(val pos: (Position, Position))
  extends PMember with PTypedDeclaration with PGlobalDeclaration with PSemanticDeclaration with PGlobalCallable {

  val typ = PPredicateType()()
  override def tokenType = TokenType.Struct
  override def symbolKind: SymbolKind.SymbolKind = SymbolKind.Struct
  override def keyword: PKeywordLang = predicate
  override def pres: Seq[(PKeywordLang, PExp)] = Seq()
  override def posts: Seq[(PKeywordLang, PExp)] = Seq()
  override def returnString: Option[String] = None
  override def bodyRange: Option[RangePosition] = body.flatMap(RangePosition(_))
}

trait PDomainMember1 extends PNode
case class PDomainFunction1(annotations: Seq[PAnnotation], function: PKeywordLang, idndef: PIdnDef, formalArgs: Seq[PAnyFormalArgDecl], typ: PType, unique: Boolean, interpretation: Option[String])(val pos: (Position, Position)) extends PDomainMember1
case class PAxiom1(annotations: Seq[PAnnotation], axiom: PKeywordLang, idndef: Option[PIdnDef], exp: PBlock[PExp])(val pos: (Position, Position)) extends PDomainMember1
case class PDomainMembers1(members: Seq[PDomainMember1])(val pos: (Position, Position)) extends PNode

case class PAnnotation(key: String, values: Seq[String])(val pos: (Position, Position)) extends PNode with HasSemanticHighlights {

  override def getSemanticHighlights: Seq[SemanticHighlight] = (key, RangePosition(this)) match {
    case ("doc", Some(sp)) => Seq(SemanticHighlight(sp, TokenType.Comment))
    case _ => Seq()
  }
}

case class PBlock[+T <: PNode](inner: T)(val pos: (Position, Position)) extends PNode

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
      case PKeywordLang(_) => Nil
      case PKeywordStmt(_) => Nil
      case PKeywordConstant(_) => Nil
      case PKeywordType(_) => Nil
      case PKeywordOperator(_) => Nil
      case POperatorSymbol(_) => Nil
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
      // case PPredicateAccess(args, pred) => args ++ Seq(pred)
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
      case PNoPerm(k) => Seq(k)
      case PFullPerm(k) => Seq(k)
      case PWildcard(k) => Seq(k)
      case PEpsilon(k) => Seq(k)
      case PAccPred(acc, loc, perm) => Seq(acc, loc, perm)
      case PEmptySeq(_) => Nil
      // case PSeqIndex(seq, idx) => Seq(seq, idx)
      case PExplicitSeq(elems) => elems
      case PRangeSeq(low, high) => Seq(low, high)
      case PSeqTake(seq, nn) => Seq(seq, nn)
      case PSeqDrop(seq, nn) => Seq(seq, nn)
      // case PSeqUpdate(seq, idx, elem) => Seq(seq, idx, elem)
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
      case PFold(fold, exp) => Seq(fold, exp)
      case PUnfold(unfold, exp) => Seq(unfold, exp)
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
      case PGoto(goto, label) => Seq(goto, label)
      case PVarAssign(target, rhs) => Seq(target, rhs)
      case PFieldAssign(field, rhs) => Seq(field, rhs)
      case PMacroAssign(call, exp) => Seq(call, exp)
      case PIf(keyword, cond, thn, elsKw, els) => Seq(keyword, cond, thn) ++ elsKw.toSeq ++ Seq(els)
      case PWhile(keyword, cond, invs, body) => Seq(keyword, cond) ++ invs.flatMap(inv => Seq(inv._1, inv._2)) ++ Seq(body)
      case PLocalVarDecl(keyword, idndef, typ, init) => Seq(keyword, idndef, typ) ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PProgram(imports, macros, domains, fields, functions, predicates, methods, extensions, _) =>
        imports ++ macros ++ domains ++ fields ++ functions ++ predicates ++ methods ++ extensions
      case PLocalImport(imprt, _) => Seq(imprt)
      case PStandardImport(imprt, _) => Seq(imprt)
      case PDomain(anns, domain, idndef, typVars, members, _) => anns ++ Seq(domain, idndef) ++ typVars ++ Seq(members)
      case PDomainMembers(funcs, axioms) => funcs ++ axioms
      case PField(anns, field, idndef, typ) => anns ++ Seq(field, idndef, typ)
      case PMethod(anns, method, idndef, args, rets, pres, posts, body) =>
        anns ++ Seq(method, idndef) ++ args ++ rets ++ pres.flatMap(c => Seq(c._1, c._2)) ++ posts.flatMap(c => Seq(c._1, c._2)) ++ body.toSeq
      case PFunction(anns, function, name, args, typ, pres, posts, body) =>
        anns ++ Seq(function, name) ++ args ++ Seq(typ) ++ pres.flatMap(c => Seq(c._1, c._2)) ++ posts.flatMap(c => Seq(c._1, c._2)) ++ body
      case PDomainFunction(anns, function, name, args, typ, _, _) =>
        anns ++ Seq(function, name) ++ args ++ Seq(typ)
      case PPredicate(anns, predicate, name, args, body) =>
        anns ++ Seq(predicate, name) ++ args ++ body
      case PAxiom(anns, axiom, idndef, exp) => anns ++ Seq(axiom) ++ idndef.toSeq ++ Seq(exp)
      case PTypeVarDecl(name) => Seq(name)
      case PDefine(define, idndef, optArgs, body) => Seq(define, idndef) ++ optArgs.getOrElse(Nil) ++ Seq(body)
      case PQuasihavoc(quasihavoc, lhs, e) =>
        Seq(quasihavoc) ++ lhs.toSeq.flatMap(lhs => Seq(lhs._1, lhs._2)) ++ Seq(e)
      case PQuasihavocall(quasihavocall, vars, cc, lhs, e) =>
        Seq(quasihavocall) ++ vars ++ Seq(cc) ++ lhs.toSeq.flatMap(lhs => Seq(lhs._1, lhs._2)) ++ Seq(e)
      case PAnnotatedExp(e, ann) => Seq(e, ann)
      case PAnnotatedStmt(s, ann) => Seq(s, ann)
      case PBlock(inner) => Seq(inner)
      case _: PAnnotation => Nil
      case t: PExtender => t.getSubnodes()
      case _: PSkip => Nil
      case _: PUnnamedFormalArgDecl => Nil
    }
  }
}
