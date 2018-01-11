/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import scala.collection.{GenTraversable, Set}
import scala.language.implicitConversions
import scala.util.parsing.input.Position
import viper.silver.ast.utility.Visitor
import viper.silver.ast.MagicWandOp
import viper.silver.FastPositions
import viper.silver.ast.utility.Rewriter.{Rewritable, StrategyBuilder}
import viper.silver.parser.TypeHelper._
import viper.silver.verifier.ParseReport


trait FastPositioned {

  /** Do not use these first three interfaces for reporting the positions.
    * They may or may not contain the rel_file field, depending on whether
    * the AST is constructed through the Parser or via the Scala interfaces. */

  /** TODO get ride of 'implicit def liftPos' of Translator.scala and make these methods private. */
  def start = FastPositions.getStart(this)
  def finish = FastPositions.getFinish(this)

  /** Used for reporting the starting position of an AST node. */
  def startPosStr = start match {
    case fp: FilePosition =>
      s"${fp.file.getFileName}@${start}"
    case _ =>
      s"${start}"
  }

  /** Used for reporting the range of positions occupied by an AST node. */
  def rangeStr = start match {
       case fp_a: FilePosition =>
      require(finish.isInstanceOf[FilePosition],
        s"start and finish positions must be instances of FilePosition at the same time")
      val fp_b = finish.asInstanceOf[FilePosition]
      if (fp_a.file == fp_b.file)
        s"${fp_a.file.getFileName}@[${start.line}.${start.column}-${finish.line}.${finish.column}]"
      else
      // An AST node should probably not spread between multiple source files, but who knows?
        s"[${fp_a.toString}--]"
    case _ =>
      s"[${start}-${finish}]"
  }

  private def setStart(p: Position) = FastPositions.setStart(this, (p))
  private def setFinish(p: Position) = FastPositions.setFinish(this, (p))

  def setPos(a: FastPositioned): this.type = {
    setStart(a.start)
    setFinish(a.finish)
    this
  }
}


/**
 * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
 * with the actual Viper abstract syntax tree.
 */
sealed trait PNode extends FastPositioned with Product with Rewritable {

  /** Returns a list of all direct sub-nodes of this node. */
  def subnodes = Nodes.subnodes(this)

  /** @see [[Visitor.reduceTree()]] */
  def reduceTree[T](f: (PNode, Seq[T]) => T) = Visitor.reduceTree(this, Nodes.subnodes)(f)

  /** @see [[Visitor.reduceWithContext()]] */
  def reduceWithContext[C, R](context: C, enter: (PNode, C) => C, combine: (PNode, C, Seq[R]) => R) = {
    Visitor.reduceWithContext(this, Nodes.subnodes)(context, enter, combine)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f: PartialFunction[PNode, Unit]) {
    Visitor.visit(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visit()]] */
  def visit(f1: PartialFunction[PNode, Unit], f2: PartialFunction[PNode, Unit]) {
    Visitor.visit(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f: PNode => Boolean) {
    Visitor.visitOpt(this, Nodes.subnodes)(f)
  }

  /** @see [[Visitor.visitOpt()]] */
  def visitOpt(f1: PNode => Boolean, f2: PNode => Unit) {
    Visitor.visitOpt(this, Nodes.subnodes, f1, f2)
  }

  /** @see [[Transformer.transform()]]  */
  def transform(pre: PartialFunction[PNode, PNode] = PartialFunction.empty)
               (recursive: PNode => Boolean = !pre.isDefinedAt(_),
                post: PartialFunction[PNode, PNode] = PartialFunction.empty,
                allowChangingNodeType: Boolean = false,
                resultCheck : PartialFunction[(PNode, PNode), Unit] = PartialFunction.empty)
               : this.type =

    Transformer.transform[this.type](this, pre)(recursive, post, allowChangingNodeType, resultCheck)

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[A](f: PartialFunction[PNode, A]) : Seq[A] =
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
  def deepCopyAll[A <: PNode]: A =
    StrategyBuilder.Slim[PNode](PartialFunction.empty).duplicateEverything.execute[A](this)

  private val _children = scala.collection.mutable.ListBuffer[PNode] ()


  var parent : PNode = null
  var index : Int = -1
  var next : PNode = null
  var prev : PNode = null

  def initProperties() {

    var ind : Int = 0
    var prev : PNode = null


    def setNodeChildConnections (node : Any) : Unit =
      node match {
        case c : PNode =>
          c.parent = this
          _children += c
          c.index = ind
          ind += 1
          c.prev = prev
          c.next = null
          if (prev != null) prev.next = c
          prev = c
          c.initProperties
        case Some (o) =>
          setNodeChildConnections (o)
          case s : GenTraversable[_] =>
          for (v <- s)
            setNodeChildConnections (v)
        case _ =>
        // Ignore other kinds of nodes
      }

    _children.clear ()
    for (c <- productIterator)
      setNodeChildConnections (c)

  }

  override def duplicate(children: scala.Seq[AnyRef]): Rewritable = {
    val dup = Transformer.parseTreeDuplicator(this, children)
    dup.setPos(this)
  }

}

object TypeHelper {
  val Int = PPrimitiv("Int")
  val Bool = PPrimitiv("Bool")
  val Perm = PPrimitiv("Perm")
  val Ref = PPrimitiv("Ref")
  val Pred = PPredicateType()
  val Wand = PWandType()
}

// Identifiers (uses and definitions)
trait PIdentifier {
  def name: String
}

case class PIdnDef(name: String) extends PNode with PIdentifier

case class PIdnUse(name: String) extends PExp with PIdentifier {
  var decl: PDeclaration = null
    /* Should be set during resolving. Intended to preserve information
     * that is needed by the translator.
     */
  override val typeSubstitutions = List(PTypeSubstitution.id)

  def forceSubstitution(ts: PTypeSubstitution) = {}
}

//case class PLocalVar

/* Formal arguments.
 * [2014-11-13 Malte] Changed type to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PFormalArgDecl(idndef: PIdnDef, var typ: PType) extends PNode with PTypedDeclaration with PLocalDeclaration

// Types
sealed trait PType extends PNode {
  def isUnknown: Boolean = this.isInstanceOf[PUnknown]
  def isValidOrUndeclared : Boolean
  def isGround : Boolean = true
//  def substitute(newTypVarsMap: Map[String, PType]): PType = this
  def substitute(ts:PTypeSubstitution) : PType
  def subNodes : Seq[PType]
  //If we add type quantification or any type binders we need to modify this
  def freeTypeVariables : Set[String] =
    subNodes.flatMap(_.freeTypeVariables).toSet union
      (this match {
        case pdt : PDomainType if pdt.isTypeVar && PTypeVar.isFreePTVName(pdt.domain.name) => Set(pdt.genericName)
        case _ => Set()
      })

  //    def isDisjoint[T](s1:Set[T],s2:Set[T]) = (s1 intersect s2).isEmpty
}


case class PPrimitiv(name: String) extends PType {
  override def substitute(ts:PTypeSubstitution) : PType = this
  override val subNodes = Seq()
  override def toString = name
  override def isValidOrUndeclared = true
}

case class PDomainType(domain: PIdnUse, args: Seq[PType]) extends PGenericType {
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
    (isTypeVar || kind==PDomainTypeKinds.Domain || kind==PDomainTypeKinds.Undeclared) &&
    args.forall(_.isValidOrUndeclared)


  def isResolved = kind != PDomainTypeKinds.Unresolved

  def isUndeclared = kind == PDomainTypeKinds.Undeclared

  override def isGround: Boolean = {
    args.forall(_.isGround) && (!isTypeVar || !PTypeVar.isFreePTVName(domain.name))
  }

  override def substitute(ts: PTypeSubstitution): PType = {
    require(kind==PDomainTypeKinds.Domain || kind==PDomainTypeKinds.TypeVar || kind==PDomainTypeKinds.Undeclared)
    if (isTypeVar)
      if (ts.isDefinedAt(domain.name))
        return ts.get(domain.name).get
      else
        return this

    val newArgs = args map (a=>a.substitute(ts))
    if (args==newArgs)
      return this

    val r = new PDomainType(domain,newArgs)
    r.kind = PDomainTypeKinds.Domain
    r
  }

  override def toString = domain.name + (if (args.isEmpty) "" else s"[${args.mkString(", ")}]")
}

object PDomainTypeKinds {
  trait Kind
  case object Unresolved extends Kind
  case object Domain extends Kind
  case object TypeVar extends Kind
  case object Undeclared extends Kind
}

object PTypeVar{
  def unapply(pt: PType) : Option[String] =
    pt match {case pdt:PDomainType if pdt.isTypeVar => Some(pdt.domain.name) case _ =>  None}
  def apply(name: String) = {
    val t = PDomainType(PIdnUse(name), Nil)
    t.kind = PDomainTypeKinds.TypeVar
    t
  }

  val sep = "#"
  //TODO: do this properly
  def isFreePTVName(s : String) = s.contains(sep)
  private var lastIndex = 0
  //Generate a unique fresh version of old
  def fresh(old: PDomainType) = {
    require(old.isTypeVar)
    val freshName = getFreshName(old.domain.name)
    lastIndex+=1
    PTypeVar(freshName)
  }
  private def getFreshName(name:String) = name+sep+lastIndex
  def freshTypeSubstitutionPTVs(tvs : Seq[PDomainType]) : PTypeRenaming = {
    require(tvs.forall(_.isTypeVar))
    freshTypeSubstitution(tvs map (tv=>tv.domain.name))
  }
  def freshTypeSubstitution(tvns : Seq[String]) : PTypeRenaming =
    {
      lastIndex+=1
      new PTypeRenaming((tvns map (tv=>tv->getFreshName(tv))).toMap)
    }
}

sealed trait PGenericType extends PType {
  def genericName : String
  def typeArguments : Seq[PType]
  override def isGround = typeArguments.forall(_.isGround)
}
sealed trait PGenericCollectionType extends PGenericType{
  def elementType : PType
  override val typeArguments = Seq(elementType)
  override def toString = genericName + s"[$elementType]"
  override val subNodes = Seq(elementType)
  override def isValidOrUndeclared = typeArguments.forall(_.isValidOrUndeclared)
}

case class PSeqType(elementType: PType) extends PType with PGenericCollectionType {
  override val genericName = "Seq"
  override def substitute(map: PTypeSubstitution) = PSeqType(elementType.substitute(map))
}
case class PSetType(elementType: PType) extends PType with PGenericCollectionType {
  override val genericName = "Set"
  override def substitute(map: PTypeSubstitution) = PSetType(elementType.substitute(map))
}
case class PMultisetType(elementType: PType) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"
  override def substitute(map: PTypeSubstitution) = PMultisetType(elementType.substitute(map))
}

/** Type used for internal nodes (e.g. typing predicate accesses) - should not be
  * the type of any expression whose value is meaningful in the translation.
  */
sealed trait PInternalType extends PType{
  override val subNodes = Seq()
  override def substitute(ts:PTypeSubstitution) = this
}

// for resolving if something cannot be typed
case class PUnknown() extends PInternalType {
  override def toString = "<error type>"
  override def isValidOrUndeclared = false
}
// used during resolving for predicate accesses
case class PPredicateType() extends PInternalType {
  override def toString = "$predicate"
  override def isValidOrUndeclared = true
}

case class PWandType() extends PInternalType {
  override def toString = "$wand"
  override def isValidOrUndeclared = true
}

///////////////////////////////////////////////////////////////////////////////////////
// Expressions
// typeSubstitutions are the possible substitutions used for type checking and inference
// The argument types are unified with the (fresh versions of) types  are
sealed trait PExp extends PNode {
  var typ: PType = PUnknown()
  def typeSubstitutions : scala.collection.Seq[PTypeSubstitution]
  def forceSubstitution(ts: PTypeSubstitution)
}

sealed trait PDecClause extends PNode

case class PDecStar() extends PDecClause

case class PDecTuple (decs: Seq[PExp]) extends PDecClause

class PTypeSubstitution(val m:Map[String,PType])  //extends Map[String,PType]()
{
  require(m.values.forall(_.isValidOrUndeclared))
  def -(key: String) = new PTypeSubstitution(m.-(key))
  def get(key: String) : Option[PType] = m.get(key)
  private def +(kv: (String, PType)): PTypeSubstitution = new PTypeSubstitution(m + kv)
  def iterator: Iterator[(String, PType)] = m.iterator
  def isDefinedAt(key : String) = contains(key)
  def keySet : Set[String] = m.keySet

  def restrict(s:Set[String]) = PTypeSubstitution(m.filter(s contains _._1))

  def map[B](f : ((String, PType)) => B) : Seq[B] =
    m.map(f).toSeq

  def contains(key : PDomainType) : Boolean = contains(key.domain.name)
  def contains(key : String) : Boolean = get(key).nonEmpty

  def substitute(a:String,b:PType) : PTypeSubstitution = {
    require(!contains(a))
    val ts = PTypeSubstitution(Map(a -> b))
    PTypeSubstitution(m.map(kv => kv._1 -> kv._2.substitute(ts)))
  }
  def *(other:PTypeSubstitution) : Option[PTypeSubstitution] =
    other.m.foldLeft(Some(this):Option[PTypeSubstitution])({
      case (Some(s),p)=>s.add(PTypeVar(p._1),p._2);
      case (None,_) => None })

  def add(a:String,b:PType): Option[PTypeSubstitution] = add(PTypeVar(a),b)

  def add(a:PType,b:PType): Option[PTypeSubstitution] = {
    val as = a.substitute(this)
    val bs = b.substitute(this)
    (as, bs) match {
      case (aa,bb) if aa == bb => Some(this)
      case (tv@PTypeVar(name), t) if PTypeVar.isFreePTVName(name) => assert(!contains(name)); Some(substitute(name,t)+(name->t))
      case (t, PTypeVar(name))    if PTypeVar.isFreePTVName(name) => add(bs,as)
      case (gt1: PGenericType, gt2: PGenericType) if gt1.genericName == gt2.genericName =>
        ((gt1.typeArguments zip gt2.typeArguments).foldLeft[Option[PTypeSubstitution]](Some(this))
          ((ss: Option[PTypeSubstitution], p: (PType, PType)) => ss match {
            case Some(sss) => sss.add(p._1,p._2)
            case None => None
          }))
      case _ => None
    }

  }

//  def apply(key:PDomainType) = apply(key.domain.name)
//  def apply(key:String) = get(key)

//  def getOrId(key:String) : String = this(key) match{ case Some(if (contains(key)) get(key) else key
  def this(s:Seq[(String,PType)]) = this(s.toMap)

//  def this(m:Map[PDomainType,PType]) = this(m.map (kv=>kv._1.domain.name->kv._2))

//  implicit def this(m:Map[String,PType]) = this(m.map (kv=>kv._1->kv._2))

//  implicit def fromMap(m:Map[String,PType]) = new PTypeSubstitution(m)
//  private def this() = this(Map())

  def isFullyReduced =
    m.values.forall(pt=> (pt.freeTypeVariables intersect m.keySet).isEmpty)

  assert(isFullyReduced)
//  assert(keySet.forall(PTypeVar.isFreePTVName))
}

object PTypeSubstitution{
  val id = new PTypeSubstitution(Seq())
  implicit def apply(m:Map[String,PType]) : PTypeSubstitution = new PTypeSubstitution(m)
  val defaultType = Int
}

class PTypeRenaming(val mm:Map[String,String])
  extends PTypeSubstitution(mm.map(kv => kv._1 -> PTypeVar(kv._2)))
{
  def +(kv: (String, String)): PTypeRenaming = new PTypeRenaming(mm + (kv._1->kv._2))
  def getS(key: String) : Option[String] = mm.get(key)

  def rename(key:String) : String = getS(key) match{ case Some(s) => s case None => key }
}



// Operator applications
sealed trait POpApp extends PExp{
  def opName : String
  def args : Seq[PExp]

  private val _typeSubstitutions = new scala.collection.mutable.MutableList[PTypeSubstitution]()
  final override def typeSubstitutions = _typeSubstitutions
  def signatures : List[PTypeSubstitution]
  def extraLocalTypeVariables : Set[PDomainType] = Set()
  def localScope : Set[PDomainType] =
    extraLocalTypeVariables union
      Set(POpApp.pRes) union
      args.indices.map(POpApp.pArg).toSet

  def forceSubstitution(ts: PTypeSubstitution) = {
    typeSubstitutions.clear(); typeSubstitutions+=ts
    typ = typ.substitute(ts)
    assert(typ.isGround)
    args.foreach(_.forceSubstitution(ts))
  }
}
object POpApp{
  //type PTypeSubstitution = Map[PDomainType,PType]
  val idPTypeSubstitution = Map[PDomainType,PType]()
  def pArgS(n:Int) = { require(n>=0); "#T"+n.toString}
  def pResS     = "#R"
  def pArg(n:Int) = { require(n>=0); PTypeVar(pArgS(n))}
  def pRes     = PTypeVar(pResS)
}

case class PCall(func: PIdnUse, args: Seq[PExp], typeAnnotated : Option[PType] = None) extends POpApp with PLocationAccess
{
  override val idnuse = func
  override val opName = func.name
  override def signatures = if (function!=null&& function.formalArgs.size == args.size) (function match{
    case pf:PFunction => List(
      new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgs(i).typ) :+ (POpApp.pRes.domain.name -> function.typ))
    )
    case pdf:PDomainFunction =>
      List(
        new PTypeSubstitution(
          args.indices.map(i => POpApp.pArg(i).domain.name -> function.formalArgs(i).typ.substitute(domainTypeRenaming.get)) :+
            (POpApp.pRes.domain.name -> pdf.typ.substitute(domainTypeRenaming.get)))
      )

  })
  else if(extfunction!=null && extfunction.formalArgs.size == args.size)( extfunction match{
    case ppa: PPredicate => List(
      new PTypeSubstitution(args.indices.map(i => POpApp.pArg(i).domain.name -> extfunction.formalArgs(i).typ) :+ (POpApp.pRes.domain.name -> Bool))
    )
  })


  else List() // this case is handled in Resolver.scala (- method check) which generates the appropriate error message

  var function : PAnyFunction = null
  var extfunction : PPredicate = null
  override def extraLocalTypeVariables = _extraLocalTypeVariables
  var _extraLocalTypeVariables : Set[PDomainType] = Set()
  var domainTypeRenaming : Option[PTypeRenaming] = None
  def isDomainFunction = domainTypeRenaming.isDefined
  var domainSubstitution : Option[PTypeSubstitution] = None
  override def forceSubstitution(ots: PTypeSubstitution) = {

    val ts = domainTypeRenaming match {
      case Some(dtr) =>
        val s3 = PTypeSubstitution(dtr.mm.map(kv => kv._1 -> (ots.get(kv._2) match {
          case Some(pt) => pt
          case None => PTypeSubstitution.defaultType
        })))
        assert(s3.m.keySet==dtr.mm.keySet)
        assert(s3.m.forall(_._2.isGround))
        domainSubstitution = Some(s3)
        dtr.mm.values.foldLeft(ots)(
          (tss,s)=> if (tss.contains(s)) tss else tss.add(s, PTypeSubstitution.defaultType).get)
      case _ => ots
    }
    super.forceSubstitution(ts)
    typeSubstitutions.clear(); typeSubstitutions+=ts
    typ = typ.substitute(ts)
    assert(typ.isGround)
    args.foreach(_.forceSubstitution(ts))
  }
}

case class PTrigger(exp: Seq[PExp]) extends PNode

case class PBinExp(left: PExp, opName: String, right: PExp) extends POpApp {

  override val args = Seq(left, right)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    opName match {
      case "++" | "union" | "intersection" | "setminus" | "subset" => Set(extraElementType)
      case _ => Set()
    }
  val signatures : List[PTypeSubstitution] = opName match {
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
      Map(POpApp.pArgS(1) -> PSetType(POpApp.pArg(0)), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> PSeqType(POpApp.pArg(0)), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(1) -> PMultisetType(POpApp.pArg(0)), POpApp.pResS -> Int)
    )
    case "++" => List(
      Map(POpApp.pArgS(0) -> PSeqType(extraElementType), POpApp.pArgS(1) -> PSeqType(extraElementType), POpApp.pResS -> PSeqType(extraElementType))
    )
    case "union" | "intersection" | "setminus" => List(
      Map(POpApp.pArgS(0) -> PSetType(extraElementType), POpApp.pArgS(1) -> PSetType(extraElementType), POpApp.pResS -> PSetType(extraElementType)),
      Map(POpApp.pArgS(0) -> PMultisetType(extraElementType), POpApp.pArgS(1) -> PMultisetType(extraElementType), POpApp.pResS -> PMultisetType(extraElementType))
    )
    case "subset" => List(
      Map(POpApp.pArgS(0) -> PSetType(extraElementType), POpApp.pArgS(1) -> PSetType(extraElementType), POpApp.pResS -> Bool),
      Map(POpApp.pArgS(0) -> PMultisetType(extraElementType), POpApp.pArgS(1) -> PMultisetType(extraElementType), POpApp.pResS -> Bool)
    )
    case _ => sys.error(s"internal error - unknown binary operator $opName")
  }
}

case class PUnExp(opName: String, exp: PExp) extends POpApp {
  override val args = Seq(exp)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    opName match {
      case "++" | "union" | "intersection" | "setminus" | "subset" => Set(extraElementType)
      case _ => Set()
    }
  override val signatures : List[PTypeSubstitution] = opName match {
    case "-" | "+" => List(
      Map(POpApp.pArgS(0) -> Int, POpApp.pResS -> Int),
      Map(POpApp.pArgS(0) -> Perm, POpApp.pResS -> Perm)
    )
    case "!" => List(
      Map(POpApp.pArgS(0) -> Bool, POpApp.pResS -> Bool)
    )
    case _ => sys.error(s"internal error - unknown unary operator $opName")
  }
}

case class PCondExp(cond: PExp, thn: PExp, els: PExp) extends POpApp
{
  override val opName = "?:"
  override val args = Seq(cond,thn,els)
  val signatures : List[PTypeSubstitution] = List(
      Map(POpApp.pArgS(0) -> Bool,POpApp.pArgS(2) -> POpApp.pArg(1), POpApp.pResS -> POpApp.pArg(1))
  )

}
// Simple literals
sealed trait PSimpleLiteral extends PExp {
  override final val typeSubstitutions = Seq(PTypeSubstitution.id)
  def forceSubstitution(ts: PTypeSubstitution) = {}
}
case class PIntLit(i: BigInt) extends PSimpleLiteral{
  typ = Int
}
case class PResultLit() extends PSimpleLiteral
case class PBoolLit(b: Boolean) extends PSimpleLiteral{
  typ = Bool
}
case class PNullLit() extends PSimpleLiteral{
  typ = Ref
}
//sealed trait PHeapOpApp extends POpApp{final override val extraLocalTypeVariables = Set()}
sealed trait PHeapOpApp extends POpApp{
//  val _typeSubstitutions : Set[PTypeSubstitution] = Set(PTypeSubstitution.id)
//  override final val typeSubstitutions = _typeSubstitutions
}
sealed trait PLocationAccess extends PHeapOpApp {
  def idnuse: PIdnUse
}

case class PFieldAccess(rcv: PExp, idnuse: PIdnUse) extends PLocationAccess{
  override final val opName = "."
  override final val args = Seq(rcv)
  override def signatures =
    if (Set(rcv.typ,idnuse.typ).forall(_.isValidOrUndeclared))
      List(PTypeSubstitution(Map(POpApp.pArgS(0) -> Ref,POpApp.pResS -> idnuse.typ)))
    else
      List()
  //setType()
}
case class PPredicateAccess(args: Seq[PExp], idnuse: PIdnUse) extends PLocationAccess{
  override final val opName = "acc"
  var predicate : PPredicate = null
  override def signatures = if (predicate == null) List() else
    List(new PTypeSubstitution(
        args.indices.map(i => POpApp.pArg(i).domain.name -> predicate.formalArgs(i).typ) :+
          (POpApp.pRes.domain.name -> Pred)))
}

case class PUnfolding(acc: PAccPred, exp: PExp) extends PHeapOpApp {
  override final val opName = "unfolding"
  override val args = Seq(acc,exp)
  override val signatures : List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Bool,POpApp.pResS -> POpApp.pArg(1)))

  //  check(e.acc.perm, Perm)
  //  check(e.acc.loc, Pred)
  //  acceptNonAbstractPredicateAccess(e.acc, "abstract predicates cannot be (un)folded")
}

case class PApplying(wand: PExp, exp: PExp) extends PHeapOpApp {
  override val opName = "applying"
  override val args = Seq(wand, exp)
  override val signatures : List[PTypeSubstitution] =
    List(Map(POpApp.pArgS(0) -> Wand, POpApp.pResS -> POpApp.pArg(1)))
}

sealed trait PBinder extends PExp{
  def body:PExp
  var _typeSubstitutions : List[PTypeSubstitution] =  null
  override def typeSubstitutions = _typeSubstitutions
  override def forceSubstitution(ts: PTypeSubstitution) = {
    _typeSubstitutions = List(ts)
    typ = typ.substitute(ts)
    body.forceSubstitution(ts)
  }
}
sealed trait PQuantifier extends PBinder with PScope{
  def vars : Seq[PFormalArgDecl]
  def triggers : Seq[PTrigger]
}
case class PExists(vars: Seq[PFormalArgDecl], body: PExp) extends PQuantifier{val triggers : Seq[PTrigger] = Seq()}
case class PForall(vars: Seq[PFormalArgDecl], triggers: Seq[PTrigger], body: PExp) extends PQuantifier

case class PForPerm(variable: PFormalArgDecl, fields: Seq[PIdnUse], body: PExp) extends PQuantifier{
  val triggers : Seq[PTrigger] = Seq()
  override val vars = Seq(variable)
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
case class PLet(exp: PExp, nestedScope: PLetNestedScope) extends PBinder{
  override val body = nestedScope.body
  override def forceSubstitution(ts: PTypeSubstitution) = {
    super.forceSubstitution(ts)
    exp.forceSubstitution(ts)
    this.nestedScope.variable.typ = exp.typ
  }
}
case class PLetNestedScope(variable: PFormalArgDecl, body: PExp) extends PNode with PScope

case class PInhaleExhaleExp(in: PExp, ex: PExp) extends PHeapOpApp{
  override val opName = "#inhale#exhale"
  override val args = Seq(in,ex)
  val signatures : List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0) -> Bool,POpApp.pArgS(1) -> Bool, POpApp.pResS -> Bool)
  )
}
case class PCurPerm(loc: PLocationAccess) extends PHeapOpApp{
  override val opName = "#perm"
  override val args = Seq(loc)
  val signatures : List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> Perm)
  )
}
case class PNoPerm() extends PSimpleLiteral{typ = Perm}
case class PFullPerm() extends PSimpleLiteral{typ = Perm}
case class PWildcard() extends PSimpleLiteral{typ = Perm}
case class PEpsilon() extends PSimpleLiteral{typ = Perm}
case class PAccPred(loc: PLocationAccess, perm: PExp) extends POpApp {
  override val opName = "acc"
  override val signatures : List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(1) -> Perm,POpApp.pResS -> Bool))
  override val args = Seq(loc,perm)
}

sealed trait POldExp extends PHeapOpApp {
  def e: PExp
  override val args = Seq(e)
  override val signatures : List[PTypeSubstitution] = List(
    Map(POpApp.pResS -> POpApp.pArg(0)))
}
case class POld(e: PExp) extends POldExp{
  override val opName = "old"
}
case class PLabelledOld(label: PIdnUse, e: PExp) extends POldExp{
  override val opName = "old#labeled"
}

sealed trait PCollectionLiteral extends POpApp{
  def pElementType : PType
  def pCollectionType(pType:PType) : PType
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
  override val signatures  : List[PTypeSubstitution] =
    List(
      ((0 until args.size) map
        (n => if (n==0) POpApp.pResS -> pCollectionType(POpApp.pArg(0)) else POpApp.pArgS(n) -> POpApp.pArg(0))).toMap
    )

  override val pElementType = args.head.typ
}
sealed trait PSeqLiteral extends PCollectionLiteral{
  override val opName = "Seq#Seq"
  def pCollectionType(pType:PType) = if (pType.isUnknown) PUnknown() else PSeqType(pType)
}
case class PEmptySeq(pElementType : PType) extends PSeqLiteral with PEmptyCollectionLiteral
case class PExplicitSeq(override val args: Seq[PExp]) extends PSeqLiteral with PExplicitCollectionLiteral
case class PRangeSeq(low: PExp, high: PExp) extends POpApp{
  override val opName = "Seq#RangeSeq"
  override val args = Seq(low,high)
  override val signatures : List[PTypeSubstitution]= List(
    Map(POpApp.pArgS(0)->Int,POpApp.pArgS(1)->Int,POpApp.pResS->PSeqType(Int)))
}
case class PSeqIndex(seq: PExp, idx: PExp) extends POpApp{
  override val opName = "Seq#At"
  override val args = Seq(seq,idx)
  override val signatures : List[PTypeSubstitution]= List(
    Map(
      POpApp.pArgS(0)->PSeqType(POpApp.pRes),
      POpApp.pArgS(1)->Int)
  )
}
case class PSeqTake(seq: PExp, n: PExp) extends POpApp{
  override val opName = "Seq#Take"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq,n)
  override val signatures : List[PTypeSubstitution]= List(
    Map(
      POpApp.pArgS(0)->PSeqType(elementType),
      POpApp.pArgS(1)->Int,
      POpApp.pResS->PSeqType(elementType)
  ))
}
case class PSeqDrop(seq: PExp, n: PExp) extends POpApp{
  override val opName = "Seq#Drop"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq,n)
  override val signatures : List[PTypeSubstitution]= List(
    Map(
      POpApp.pArgS(0)->PSeqType(elementType),
      POpApp.pArgS(1)->Int,
      POpApp.pResS->PSeqType(elementType)
    ))
}
case class PSeqUpdate(seq: PExp, idx: PExp, elem: PExp) extends POpApp{
  override val opName = "Seq#update"
  val elementType = POpApp.pArg(2)
  override val args = Seq(seq,idx,elem)
  override val signatures : List[PTypeSubstitution] = List(
    Map(
      POpApp.pArgS(0)->PSeqType(elementType),
      POpApp.pArgS(1)->Int,
      POpApp.pResS->PSeqType(elementType)
    ))
  override val extraLocalTypeVariables = Set(elementType)
}

case class PSize(seq: PExp) extends POpApp{
  override val opName = "Seq#size"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq)
  override val signatures : List[PTypeSubstitution] = List(
    Map(POpApp.pArgS(0)->PSeqType(elementType),POpApp.pResS->Int),
    Map(POpApp.pArgS(0)->PSetType(elementType),POpApp.pResS->Int),
    Map(POpApp.pArgS(0)->PMultisetType(elementType),POpApp.pResS->Int)
  )
}

sealed trait PSetLiteral extends PCollectionLiteral{
  override val opName = "Set#Set"
  def pCollectionType(pType:PType) = if (pType.isUnknown) PUnknown() else PSetType(pType)
}
case class PEmptySet(pElementType : PType) extends PSetLiteral with PEmptyCollectionLiteral
case class PExplicitSet(args: Seq[PExp]) extends PSetLiteral with PExplicitCollectionLiteral

sealed trait PMultiSetLiteral extends PCollectionLiteral{
  override val opName = "Multiset#Multiset"
  def pCollectionType(pType:PType) = if (pType.isUnknown) PUnknown() else PMultisetType(pType)
}
case class PEmptyMultiset(override val pElementType  : PType) extends PMultiSetLiteral with PEmptyCollectionLiteral

case class PExplicitMultiset(override val args: Seq[PExp]) extends PMultiSetLiteral with PExplicitCollectionLiteral

///////////////////////////////////////////////////////////////////////////
// Statements
sealed trait PStmt extends PNode {
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
case class PSeqn(ss: Seq[PStmt]) extends PStmt with PScope
case class PFold(e: PExp) extends PStmt
case class PUnfold(e: PExp) extends PStmt
case class PPackageWand(wand: PExp, proofScript: PSeqn) extends PStmt
case class PApplyWand(e: PExp) extends PStmt
case class PExhale(e: PExp) extends PStmt
case class PAssert(e: PExp) extends PStmt
case class PAssume(e: PExp) extends PStmt
case class PInhale(e: PExp) extends PStmt
case class PVarAssign(idnuse: PIdnUse, rhs: PExp) extends PStmt
case class PFieldAssign(fieldAcc: PFieldAccess, rhs: PExp) extends PStmt
case class PIf(cond: PExp, thn: PSeqn, els: PSeqn) extends PStmt
case class PWhile(cond: PExp, invs: Seq[PExp], body: PSeqn) extends PStmt
case class PFresh(vars: Seq[PIdnUse]) extends PStmt
case class PConstraining(vars: Seq[PIdnUse], stmt: PSeqn) extends PStmt
case class PLocalVarDecl(idndef: PIdnDef, typ: PType, init: Option[PExp]) extends PStmt with PTypedDeclaration with PLocalDeclaration
case class PMethodCall(targets: Seq[PIdnUse], method: PIdnUse, args: Seq[PExp]) extends PStmt
case class PLabel(idndef: PIdnDef, invs: Seq[PExp]) extends PStmt with PLocalDeclaration
case class PGoto(targets: PIdnUse) extends PStmt
case class PTypeVarDecl(idndef: PIdnDef) extends PLocalDeclaration
case class PMacroRef(idnuse : PIdnUse) extends PStmt
case class PDefine(idndef: PIdnDef, args: Option[Seq[PIdnDef]], body: PNode) extends PStmt with PLocalDeclaration
case class PSkip() extends PStmt

sealed trait PNewStmt extends PStmt {
  def target: PIdnUse
}

/* x := new(f1, ..., fn) */
case class PRegularNewStmt(target: PIdnUse, fields: Seq[PIdnUse]) extends PNewStmt

/* x := new(*) */
case class PStarredNewStmt(target: PIdnUse) extends PNewStmt

object PNewStmt {
  def apply(target: PIdnUse): PStarredNewStmt = PStarredNewStmt(target)

  def apply(target: PIdnUse, fields: Seq[PIdnUse]): PRegularNewStmt = PRegularNewStmt(target, fields)

  def apply(target: PIdnUse, fields: Option[Seq[PIdnUse]]): PNewStmt = fields match {
    case None => PStarredNewStmt(target)
    case Some(fs) => PRegularNewStmt(target, fs)
  }

  def unapply(s: PNewStmt): Option[(PIdnUse, Option[Seq[PIdnUse]])] = s match {
    case PRegularNewStmt(target, fields) => Some((target, Some(fields)))
    case PStarredNewStmt(target) => Some((s.target, None))
  }
}

sealed trait PScope extends PNode {
  val scopeId = PScope.uniqueId()
}

object PScope {
  type Id = Long

  private[this] var counter: Id = 0L

  private def uniqueId() = {
    val id = counter
    counter = counter + 1

    id
  }
}

// Declarations
/** An entity is a declaration (named) or an error node */
sealed trait PEntity

sealed trait PDeclaration extends PNode with PEntity {
  def idndef: PIdnDef
}

sealed trait PGlobalDeclaration extends PDeclaration
sealed trait PLocalDeclaration extends PDeclaration

sealed trait PTypedDeclaration extends PDeclaration {
  def typ: PType
}
abstract class PErrorEntity(name: String) extends PEntity


// a member (like method or axiom) that is its own name scope
sealed trait PMember extends PDeclaration with PScope {
//  def idndef: PIdnDef
}

sealed trait PAnyFunction extends PMember with PGlobalDeclaration with PTypedDeclaration{
  def idndef: PIdnDef
  def formalArgs: Seq[PFormalArgDecl]
  def typ: PType
}
case class PProgram(imports: Seq[PImport], macros: Seq[PDefine], domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod], errors: Seq[ParseReport]) extends PNode
case class PImport(file: String) extends PNode
case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: Option[PStmt]) extends PMember with PGlobalDeclaration
case class PDomain(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], funcs: Seq[PDomainFunction], axioms: Seq[PAxiom]) extends PMember with PGlobalDeclaration
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[PExp], posts: Seq[PExp], decs: Option[PDecClause], body: Option[PExp]) extends PAnyFunction
case class PDomainFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, unique: Boolean)(val domainName:PIdnUse) extends PAnyFunction
case class PAxiom(idndef: PIdnDef, exp: PExp)(val domainName:PIdnUse) extends PScope with PGlobalDeclaration  //urij: this was not a declaration before - but the constructor of Program would complain on name clashes
case class PField(idndef: PIdnDef, typ: PType) extends PMember with PTypedDeclaration with PGlobalDeclaration
case class PPredicate(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: Option[PExp]) extends PMember with PTypedDeclaration with PGlobalDeclaration{
  val typ = PPredicateType()
}

case class PDomainFunction1(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, unique: Boolean) extends FastPositioned
case class PAxiom1(idndef: PIdnDef, exp: PExp) extends FastPositioned

/**
 * A entity represented by names for whom we have seen more than one
 * declaration so we are unsure what is being represented.
 */
case class PMultipleEntity() extends PErrorEntity("multiple")

/**
 * An unknown entity, represented by names whose declarations are missing.
 */
case class PUnknownEntity() extends PErrorEntity("unknown")


/**
 * Utility methods for parser parserAST nodes.
 */
object Nodes {

  /**
   * See PNode.subnodes.
   */
  def subnodes(n: PNode): Seq[PNode] = {
    n match {
      case PIdnDef(name) => Nil
      case PIdnUse(name) => Nil
      case PFormalArgDecl(idndef, typ) => Seq(idndef, typ)
      case PPrimitiv(name) => Nil
      case PDomainType(domain, args) => Seq(domain) ++ args
      case PSeqType(elemType) => Seq(elemType)
      case PSetType(elemType) => Seq(elemType)
      case PMultisetType(elemType) => Seq(elemType)
      case PUnknown() => Nil
      case PBinExp(left, op, right) => Seq(left, right)
      case PUnExp(op, exp) => Seq(exp)
      case PTrigger(exp) => exp
      case PIntLit(i) => Nil
      case PBoolLit(b) => Nil
      case PNullLit() => Nil
      case PPredicateType() => Nil
      case PWandType() => Nil
      case PResultLit() => Nil
      case PFieldAccess(rcv, field) => Seq(rcv, field)
      case PPredicateAccess(args, pred) => args ++ Seq(pred)
      case PCall(func, args, optType) => Seq(func) ++ args ++ (optType match { case Some(t) => Seq(t) case None => Nil})
      case PUnfolding(acc, exp) => Seq(acc, exp)
      case PApplying(wand, exp) => Seq(wand, exp)
      case PExists(vars, exp) => vars ++ Seq(exp)
      case PLabelledOld(id, e) => Seq(id, e)
      case po: POldExp => Seq(po.e)
      case PLet(exp, nestedScope) => Seq(exp, nestedScope)
      case PLetNestedScope(variable, body) => Seq(variable, body)
      case PForall(vars, triggers, exp) => vars ++ triggers ++ Seq(exp)
      case PForPerm(v,fields, expr) => v +: fields :+ expr
      case PCondExp(cond, thn, els) => Seq(cond, thn, els)
      case PInhaleExhaleExp(in, ex) => Seq(in, ex)
      case PCurPerm(loc) => Seq(loc)
      case PNoPerm() => Nil
      case PFullPerm() => Nil
      case PWildcard() => Nil
      case PEpsilon() => Nil
      case PAccPred(loc, perm) => Seq(loc, perm)
      case PEmptySeq(_) => Nil
      case PExplicitSeq(elems) => elems
      case PRangeSeq(low, high) => Seq(low, high)
      case PSeqIndex(seq, idx) => Seq(seq, idx)
      case PSeqTake(seq, nn) => Seq(seq, nn)
      case PSeqDrop(seq, nn) => Seq(seq, nn)
      case PSeqUpdate(seq, idx, elem) => Seq(seq, idx, elem)
      case PSize(seq) => Seq(seq)

      case PEmptySet(t) => Seq(t)
      case PExplicitSet(elems) => elems
      case PEmptyMultiset(t) => Seq(t)
      case PExplicitMultiset(elems) => elems
      case PMacroRef(name) => Nil
      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
      case PPackageWand(exp, proofScript) => Seq(exp, proofScript)
      case PApplyWand(exp) => Seq(exp)
      case PExhale(exp) => Seq(exp)
      case PAssert(exp) => Seq(exp)
      case PInhale(exp) => Seq(exp)
      case PAssume(exp) => Seq(exp)
      case PRegularNewStmt(target, fields) => Seq(target) ++ fields
      case PStarredNewStmt(target) => Seq(target)
      case PMethodCall(targets, method, args) => targets ++ Seq(method) ++ args
      case PLabel(name, invs) => Seq(name) ++ invs
      case PGoto(label) => Seq(label)
      case PVarAssign(target, rhs) => Seq(target, rhs)
      case PFieldAssign(field, rhs) => Seq(field, rhs)
      case PIf(cond, thn, els) => Seq(cond, thn, els)
      case PWhile(cond, invs, body) => Seq(cond) ++ invs ++ Seq(body)
      case PLocalVarDecl(idndef, typ, init) => Seq(idndef, typ) ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PFresh(vars) => vars
      case PConstraining(vars, stmt) => vars ++ Seq(stmt)
      case PProgram(files, macros, domains, fields, functions, predicates, methods, errors) =>
        domains ++ fields ++ functions ++ predicates ++ methods
      case PImport(file) =>
        Seq()
      case PDomain(idndef, typVars, funcs, axioms) => Seq(idndef) ++ typVars ++ funcs ++ axioms
      case PField(idndef, typ) => Seq(idndef, typ)
      case PMethod(idndef, args, rets, pres, posts, body) =>
        Seq(idndef) ++ args ++ rets ++ pres ++ posts ++ body.toSeq
      case PFunction(name, args, typ, pres, posts, dec, body) =>
        Seq(name) ++ args ++ Seq(typ) ++ pres ++ posts ++ dec ++ body
      case PDomainFunction(name, args, typ, unique) =>
        Seq(name) ++ args ++ Seq(typ)
      case PPredicate(name, args, body) =>
        Seq(name) ++ args ++ body
      case PAxiom(idndef, exp) => Seq(idndef, exp)
      case PTypeVarDecl(name) => Seq(name)
      case PDecTuple(exp) => exp
      case PDecStar() => Nil
      case PDefine(idndef, optArgs, body) => Seq(idndef) ++ optArgs.getOrElse(Nil) ++ Seq(body)
      case _: PSkip => Nil
    }
  }
}
