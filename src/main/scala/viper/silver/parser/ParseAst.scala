/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.parser

import org.kiama.util.Positions
import viper.silver.ast.MagicWandOp
import viper.silver.parser.PExp.PTypeSubstitution
import scala.util.parsing.input.Position
import org.kiama.attribution.Attributable
import viper.silver.ast.utility.Visitor
import TypeHelper._
import java.nio.file.Path

/**
 * This is a trait to ease interfacing with the changed Kiama interface - it no-longer provides Positioned as a trait, but rather a global Positions object..
 */

trait KiamaPositioned {
  def start = Positions.getStart(this)
  def setStart(p:Position) = Positions.setStart(this,p)
  def setPos(a:Any) : this.type = Positions.dupPos(a,this)
  def finish = Positions.getFinish(this)
  def setFinish(p:Position) = Positions.setFinish(this,p)
}

/**
 * The root of the parser abstract syntax tree.  Note that we prefix all nodes with `P` to avoid confusion
 * with the actual SIL abstract syntax tree.
 */
sealed trait PNode extends KiamaPositioned with Attributable {
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
                post: PartialFunction[PNode, PNode] = PartialFunction.empty)
               : this.type =

    Transformer.transform[this.type](this, pre)(recursive, post)

  /** @see [[Visitor.deepCollect()]] */
  def deepCollect[A](f: PartialFunction[PNode, A]) : Seq[A] =
    Visitor.deepCollect(Seq(this), Nodes.subnodes)(f)

  /** @see [[Visitor.shallowCollect()]] */
  def shallowCollect[R](f: PartialFunction[PNode, R]): Seq[R] =
    Visitor.shallowCollect(Seq(this), Nodes.subnodes)(f)
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
  override val localTypeSubstitutions = null
    /* Should be set during resolving. Intended to preserve information
     * that is needed by the translator.
     */
}

//case class PLocalVar

/* Formal arguments.
 * [2014-11-13 Malte] Changed typ to be a var, so that it can be updated
 * during type-checking. The use-case are let-expressions, where requiring an
 * explicit type in the binding of the variable, i.e., "let x: T = e1 in e2",
 * would be rather cumbersome.
 */
case class PFormalArgDecl(idndef: PIdnDef, var typ: PType) extends PNode with PTypedDeclaration with PLocalDeclaration

// Types
sealed trait PType extends PNode {
  def isUnknown: Boolean = this.isInstanceOf[PUnknown]
  def isConcrete: Boolean = true
  def substitute(newTypVarsMap: Map[String, PType]): PType = this
}

case class PPrimitiv(name: String) extends PType {
  override def toString = name
}

case class PDomainType(domain: PIdnUse, args: Seq[PType]) extends PGenericType {
  val genericName = domain.name
  override val typeArguments = args //if (kind==PDomainTypeKinds.Domain)
  var kind: PDomainTypeKinds.Kind = PDomainTypeKinds.Unresolved

  /* This class is also used to represent type variables, as they cannot
   * be distinguished syntactically from domain types without generic arguments.
   * For type variables, we have args.length = 0
   */
  def isTypeVar = kind == PDomainTypeKinds.TypeVar

  def isUndeclared = kind == PDomainTypeKinds.Undeclared

  override def isConcrete: Boolean = {
    args.forall(_.isConcrete) && !isTypeVar
  }

  override def substitute(newTypVarsMap: Map[String, PType]): PType = {
    if (isTypeVar && newTypVarsMap.isDefinedAt(domain.name)) {
      return newTypVarsMap.get(domain.name).get
    }

    val newArgs = args map {
      case PTypeVar(name) if newTypVarsMap.isDefinedAt(name) => newTypVarsMap.get(name).get
      case t => t
    }

    PDomainType(domain, newArgs)
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

object PTypeVar {
  def unapply(p: PDomainType) = if (p.isTypeVar) Some(p.domain.name) else None
  def apply(name: String) = {
    val t = PDomainType(PIdnUse(name), Nil)
    t.kind = PDomainTypeKinds.TypeVar
    t
  }

  val sep = "#"
  private var lastIndex = 0
  //Generate a unique fresh version of old
  def fresh(old: PDomainType) = {
    require(old.isTypeVar)
    val freshName = old.domain.name+sep+lastIndex
    lastIndex+=1
    PTypeVar(freshName)
  }
}

sealed trait PGenericType extends PType {
  def genericName : String
  def typeArguments : Seq[PType]
  override def isConcrete = typeArguments.forall(_.isConcrete)
}
sealed trait PGenericCollectionType extends PGenericType{
  val elementType : PType
  override val typeArguments = Seq(elementType)
  override def toString = genericName + s"[$elementType]"
}

case class PSeqType(elementType: PType) extends PType with PGenericCollectionType {
  override val genericName = "Seq"
  override def substitute(map: Map[String, PType]) = PSeqType(elementType.substitute(map))
}
case class PSetType(elementType: PType) extends PType with PGenericCollectionType {
  override val genericName = "Set"
  override def substitute(map: Map[String, PType]) = PSetType(elementType.substitute(map))
}
case class PMultisetType(elementType: PType) extends PType with PGenericCollectionType {
  override val genericName = "Multiset"
  override def substitute(map: Map[String, PType]) = PMultisetType(elementType.substitute(map))
}

/** Type used for internal nodes (e.g. typing predicate accesses) - should not be
  * the type of any expression whose value is meaningful in the translation.
  */
sealed trait PInternalType extends PType

// for resolving if something cannot be typed
case class PUnknown() extends PInternalType {
  override def toString = "<error type>"
}
// used during resolving for predicate accesses
case class PPredicateType() extends PInternalType {
  override def toString = "$predicate"
}

case class PWandType() extends PInternalType {
  override def toString = "$wand"
}

///////////////////////////////////////////////////////////////////////////////////////
// Expressions
// typeSubstitutions are the possible substitutions used for type checking and inference
// The argument types are unified with the (fresh versions of) types  are
sealed trait PExp extends PNode {
  var typ: PType = PUnknown()
  def typeSubstitutions = new scala.collection.mutable.HashSet[PTypeSubstitution]()
  def localTypeSubstitutions : Set[PTypeSubstitution]
  val extraLocalTypeVariables : Set[PDomainType] = Set()
}
object PExp{
  type PTypeSubstitution = Map[PDomainType,PType]
  val idPTypeSubstitution = Map[PDomainType,PType]()
  def pArgTypeVar(n:Int) = { require(n>=0); PTypeVar("#T"+n.toString)}
  def pResultTypeVar     = PTypeVar("#R")
}

// Operator applications
sealed trait POpApp extends PExp{
  def opName : String
  def args : Seq[PExp]
}

case class PFunctApp(func: PIdnUse, args: Seq[PExp]) extends POpApp
{
  override val opName = func.name
  var localTypeSubstitutions = null
}
case class PBinExp(left: PExp, opName: String, right: PExp) extends POpApp {
  override val args = Seq(left, right)
  val extraElementType = PTypeVar("#E")
  override val extraLocalTypeVariables: Set[PDomainType] =
    opName match {
      case "++" | "union" | "intersection" | "setminus" | "subset" => Set(extraElementType)
      case _ => Set()
    }
  val localTypeSubstitutions = opName match {
    case "+" | "-" => Set(
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Int),
      Map(PExp.pArgTypeVar(0) -> Perm, PExp.pArgTypeVar(1) -> Perm, PExp.pResultTypeVar -> Perm)
    )
    case "*" => Set(
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Int),
      Map(PExp.pArgTypeVar(0) -> Perm, PExp.pArgTypeVar(1) -> Perm, PExp.pResultTypeVar -> Perm),
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pArgTypeVar(1) -> Perm, PExp.pResultTypeVar -> Perm)
    )
    case "/" => Set(
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Perm),
      Map(PExp.pArgTypeVar(0) -> Perm, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Perm)
    )
    case "\\" | "%" => Set(
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Int))
    case "<" | "<=" | ">" | ">=" => Set(
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Bool),
      Map(PExp.pArgTypeVar(0) -> Perm, PExp.pArgTypeVar(1) -> Int, PExp.pResultTypeVar -> Bool))
    case "==" | "!=" => Set(
      Map(PExp.pArgTypeVar(1) -> PExp.pArgTypeVar(0), PExp.pResultTypeVar -> Bool))
    case "&&" | "||" | "<==>" | "==>" => Set(
      Map(PExp.pArgTypeVar(1) -> Bool, PExp.pArgTypeVar(0) -> Bool, PExp.pResultTypeVar -> Bool))
    case MagicWandOp.op => Set(
      Map(PExp.pArgTypeVar(1) -> Bool, PExp.pArgTypeVar(0) -> Bool, PExp.pResultTypeVar -> Wand))
    case "in" => Set(
      Map(PExp.pArgTypeVar(1) -> PSetType(PExp.pArgTypeVar(0)), PExp.pResultTypeVar -> Bool),
      Map(PExp.pArgTypeVar(1) -> PSeqType(PExp.pArgTypeVar(0)), PExp.pResultTypeVar -> Bool),
      Map(PExp.pArgTypeVar(1) -> PMultisetType(PExp.pArgTypeVar(0)), PExp.pResultTypeVar -> Int)
    )
    case "++" => Set(
      Map(PExp.pArgTypeVar(0) -> PSeqType(extraElementType), PExp.pArgTypeVar(1) -> PSeqType(extraElementType), PExp.pResultTypeVar -> PSeqType(extraElementType))
    )
    case "union" | "intersection" | "setminus" => Set(
      Map(PExp.pArgTypeVar(0) -> PSetType(extraElementType), PExp.pArgTypeVar(1) -> PSetType(extraElementType), PExp.pResultTypeVar -> PSetType(extraElementType)),
      Map(PExp.pArgTypeVar(0) -> PMultisetType(extraElementType), PExp.pArgTypeVar(1) -> PMultisetType(extraElementType), PExp.pResultTypeVar -> PMultisetType(extraElementType))
    )
    case "subset" => Set(
      Map(PExp.pArgTypeVar(0) -> PSetType(extraElementType), PExp.pArgTypeVar(1) -> PSetType(extraElementType), PExp.pResultTypeVar -> Bool),
      Map(PExp.pArgTypeVar(0) -> PMultisetType(extraElementType), PExp.pArgTypeVar(1) -> PMultisetType(extraElementType), PExp.pResultTypeVar -> Bool)
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
  val localTypeSubstitutions = opName match {
    case "-" | "+" => Set(
      Map(PExp.pArgTypeVar(0) -> Int, PExp.pResultTypeVar -> Int),
      Map(PExp.pArgTypeVar(0) -> Perm, PExp.pResultTypeVar -> Perm)
    )
    case "!" => Set(
      Map(PExp.pArgTypeVar(0) -> Bool, PExp.pResultTypeVar -> Bool)
    )
    case _ => sys.error(s"internal error - unknown unary operator $opName")
  }
}

// Simple literals
trait PSimpleLiteral extends PExp {
  val typeSubstitutions = Set(PExp.idPTypeSubstitution)
  val localTypeSubstitutions = Set()
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
sealed trait PLocationAccess extends PExp {
  def idnuse: PIdnUse
}
case class PFieldAccess(rcv: PExp, idnuse: PIdnUse) extends PLocationAccess
case class PPredicateAccess(args: Seq[PExp], idnuse: PIdnUse) extends PLocationAccess

sealed trait PUnFoldingExp extends PExp {
  def acc: PAccPred
  def exp: PExp
}

case class PUnfolding(acc: PAccPred, exp: PExp) extends PUnFoldingExp
case class PFolding(acc: PAccPred, exp: PExp) extends PUnFoldingExp

case class PApplying(wand: PExp, exp: PExp) extends PExp
case class PPackaging(wand: PExp, exp: PExp) extends PExp

case class PExists(variable: Seq[PFormalArgDecl], exp: PExp) extends PExp with PScope
case class PForall(variable: Seq[PFormalArgDecl], triggers: Seq[Seq[PExp]], exp: PExp) extends PExp with PScope
case class PForPerm(variable: PFormalArgDecl, fields: Seq[PIdnUse], exp: PExp) extends PExp with PScope
case class PCondExp(cond: PExp, thn: PExp, els: PExp) extends PExp
case class PInhaleExhaleExp(in: PExp, ex: PExp) extends PExp
case class PCurPerm(loc: PLocationAccess) extends PExp
case class PNoPerm() extends PSimpleLiteral{typ = Perm}
case class PFullPerm() extends PSimpleLiteral{typ = Perm}
case class PWildcard() extends PSimpleLiteral{typ = Perm}
case class PEpsilon() extends PSimpleLiteral{typ = Perm}
case class PAccPred(loc: PLocationAccess, perm: PExp) extends POpApp {
  typ = Bool
  override val opName = "acc"
  override val localTypeSubstitutions = Set(Map(PExp.pArgTypeVar(1) -> Perm))
  override val args = Seq(loc,perm)
}

sealed trait POldExp extends PExp { def e: PExp }
case class POld(e: PExp) extends POldExp
case class PLabelledOld(label: PIdnUse, e: PExp) extends POldExp
case class PApplyOld(e: PExp) extends POldExp

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
case class PLet(exp: PExp, nestedScope: PLetNestedScope) extends PExp
case class PLetNestedScope(variable: PFormalArgDecl, body: PExp) extends PExp with PScope

sealed trait PCollectionLiteral extends POpApp{
  def pElementType : PType
  def pCollectionType(pType:PType) : PType
  def getLocalTypeSubstitutions(numArgs : Int) = {
    require(numArgs >= 0)
    Set(
      (0 until numArgs-1) map
        (n => if (n==0) PExp.pResultTypeVar -> pCollectionType(pElementType) else PExp.pArgTypeVar(_) -> PExp.pArgTypeVar(0)) toMap
    )
  }
  def getLocalTypeSubstitutions(elemType : PType) = Set(
    PExp.pResultTypeVar -> pCollectionType(elemType)
  )
  typ = pCollectionType(pElementType)
}

sealed trait PEmptyCollectionLiteral extends PCollectionLiteral {
  override val localTypeSubstitutions = getLocalTypeSubstitutions(pElementType)
  override val args = Seq()
}
sealed trait PExplicitCollectionLiteral extends PCollectionLiteral {
  override val localTypeSubstitutions = getLocalTypeSubstitutions(args.size)
  override val pElementType = args.head.typ
}
sealed trait PSeqLiteral extends PCollectionLiteral{
  override val opName = "Seq#Seq"
  def pCollectionType(pType:PType) = if (pType.isUnknown) PUnknown() else PSeqType(pType)
}

case class PEmptySeq(pElementType : PType) extends PSeqLiteral with PEmptyCollectionLiteral{
}
case class PExplicitSeq(override val args: Seq[PExp]) extends PSeqLiteral with PExplicitCollectionLiteral
case class PRangeSeq(low: PExp, high: PExp) extends POpApp{
  override val opName = "Seq#RangeSeq"
  override val args = Seq(low,high)
  override val localTypeSubstitutions = Set(
    Map(PExp.pArgTypeVar(0)->Int,PExp.pArgTypeVar(1)->Int,PExp.pResultTypeVar->Int))
}
case class PSeqIndex(seq: PExp, idx: PExp) extends POpApp{
  override val opName = "Seq#At"
  override val args = Seq(seq,idx)
  override val localTypeSubstitutions = Set(
    Map(
      PExp.pArgTypeVar(0)->PSeqType(PExp.pArgTypeVar(1)),
      PExp.pResultTypeVar->PExp.pArgTypeVar(1))
  )
}
case class PSeqTake(seq: PExp, n: PExp) extends POpApp{
  override val opName = "Seq#Take"
  val elementType = PTypeVar("#E")
  override val args = Seq(seq,n)
  override val localTypeSubstitutions = Set(
    Map(
      PExp.pArgTypeVar(0)->PSeqType(elementType),
      PExp.pArgTypeVar(1)->Int,
      PExp.pResultTypeVar->PSeqType(elementType)
  ))
  override val extraLocalTypeVariables = Set(elementType)
}
case class PSeqDrop(seq: PExp, n: PExp) extends POpApp{
  override val opName = "Seq#Drop"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq,n)
  override val localTypeSubstitutions = Set(
    Map(
      PExp.pArgTypeVar(0)->PSeqType(elementType),
      PExp.pArgTypeVar(1)->Int,
      PExp.pResultTypeVar->PSeqType(elementType)
    ))
}
case class PSeqUpdate(seq: PExp, idx: PExp, elem: PExp) extends POpApp{
  override val opName = "Seq#update"
  val elementType = PExp.pArgTypeVar(2)
  override val args = Seq(seq,idx,elem)
  override val localTypeSubstitutions = Set(
    Map(
      PExp.pArgTypeVar(0)->PSeqType(elementType),
      PExp.pArgTypeVar(1)->Int,
      PExp.pResultTypeVar->PSeqType(elementType)
    ))
  override val extraLocalTypeVariables = Set(elementType)
}

case class PSize(seq: PExp) extends POpApp{
  override val opName = "Seq#size"
  val elementType = PTypeVar("#E")
  override val extraLocalTypeVariables = Set(elementType)
  override val args = Seq(seq)
  override val localTypeSubstitutions = Set(
    Map(
    PExp.pArgTypeVar(0)->PSeqType(elementType),
    PExp.pResultTypeVar->Int
    ))
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
case class PSeqn(ss: Seq[PStmt]) extends PStmt
case class PFold(e: PExp) extends PStmt
case class PUnfold(e: PExp) extends PStmt
case class PPackageWand(wand: PExp) extends PStmt
case class PApplyWand(e: PExp) extends PStmt
case class PExhale(e: PExp) extends PStmt
case class PAssert(e: PExp) extends PStmt
case class PInhale(e: PExp) extends PStmt
case class PNewStmt(target: PIdnUse, Fields: Option[Seq[PIdnUse]]) extends PStmt
case class PVarAssign(idnuse: PIdnUse, rhs: PExp) extends PStmt
case class PFieldAssign(fieldAcc: PFieldAccess, rhs: PExp) extends PStmt
case class PIf(cond: PExp, thn: PStmt, els: PStmt) extends PStmt
case class PWhile(cond: PExp, invs: Seq[PExp], body: PStmt) extends PStmt
case class PFresh(vars: Seq[PIdnUse]) extends PStmt
case class PConstraining(vars: Seq[PIdnUse], stmt: PStmt) extends PStmt
case class PLocalVarDecl(idndef: PIdnDef, typ: PType, init: Option[PExp]) extends PStmt with PTypedDeclaration with PLocalDeclaration
case class PMethodCall(targets: Seq[PIdnUse], method: PIdnUse, args: Seq[PExp]) extends PStmt
case class PLabel(idndef: PIdnDef) extends PStmt with PLocalDeclaration
case class PGoto(targets: PIdnUse) extends PStmt
case class PTypeVarDecl(idndef: PIdnDef) extends PLocalDeclaration

case class PLetWand(idndef: PIdnDef, exp: PExp) extends PStmt with PLocalDeclaration
case class PDefine(idndef: PIdnDef, args: Option[Seq[PIdnDef]], exp: PExp) extends PStmt with PLocalDeclaration
case class PSkip() extends PStmt

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

case class PProgram(file: Path, domains: Seq[PDomain], fields: Seq[PField], functions: Seq[PFunction], predicates: Seq[PPredicate], methods: Seq[PMethod]) extends PNode
case class PMethod(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], formalReturns: Seq[PFormalArgDecl], pres: Seq[PExp], posts: Seq[PExp], body: PStmt) extends PMember with PGlobalDeclaration
case class PDomain(idndef: PIdnDef, typVars: Seq[PTypeVarDecl], funcs: Seq[PDomainFunction], axioms: Seq[PAxiom]) extends PMember with PGlobalDeclaration
case class PFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, pres: Seq[PExp], posts: Seq[PExp], body: Option[PExp]) extends PMember with PGlobalDeclaration with PTypedDeclaration
case class PDomainFunction(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, unique: Boolean)(val domainName:PIdnUse) extends PMember with PGlobalDeclaration with PTypedDeclaration
case class PAxiom(idndef: PIdnDef, exp: PExp)(val domainName:PIdnUse) extends PScope with PGlobalDeclaration  //urij: this was not a declaration before - but the constructor of Program would complain on name clashes
case class PField(idndef: PIdnDef, typ: PType) extends PMember with PTypedDeclaration with PGlobalDeclaration
case class PPredicate(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], body: Option[PExp]) extends PMember with PTypedDeclaration with PGlobalDeclaration{
  val typ = PPredicateType()
}

case class PDomainFunction1(idndef: PIdnDef, formalArgs: Seq[PFormalArgDecl], typ: PType, unique: Boolean) extends KiamaPositioned with Attributable
case class PAxiom1(idndef: PIdnDef, exp: PExp) extends KiamaPositioned with Attributable

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
      case PIntLit(i) => Nil
      case PBoolLit(b) => Nil
      case PNullLit() => Nil
      case PPredicateType() => Nil
      case PWandType() => Nil
      case PResultLit() => Nil
      case PFieldAccess(rcv, field) => Seq(rcv, field)
      case PPredicateAccess(args, pred) => args ++ Seq(pred)
      case PFunctApp(func, args) => Seq(func) ++ args
      case e: PUnFoldingExp => Seq(e.acc, e.exp)
      case PApplying(wand, in) => Seq(wand, in)
      case PPackaging(wand, in) => Seq(wand, in)
      case PExists(vars, exp) => vars ++ Seq(exp)
      case po: POldExp => Seq(po.e)
      case PLet(exp, nestedScope) => Seq(exp, nestedScope)
      case PLetNestedScope(variable, body) => Seq(variable, body)
      case PForall(vars, triggers, exp) => vars ++ triggers.flatten ++ Seq(exp)
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

      case PSeqn(ss) => ss
      case PFold(exp) => Seq(exp)
      case PUnfold(exp) => Seq(exp)
      case PPackageWand(exp) => Seq(exp)
      case PApplyWand(exp) => Seq(exp)
      case PExhale(exp) => Seq(exp)
      case PAssert(exp) => Seq(exp)
      case PInhale(exp) => Seq(exp)
      case PNewStmt(target, fields) => Seq(target) ++ fields.getOrElse(Seq())
      case PMethodCall(targets, method, args) => targets ++ Seq(method) ++ args
      case PLabel(name) => Seq(name)
      case PGoto(label) => Seq(label)
      case PVarAssign(target, rhs) => Seq(target, rhs)
      case PFieldAssign(field, rhs) => Seq(field, rhs)
      case PIf(cond, thn, els) => Seq(cond, thn, els)
      case PWhile(cond, invs, body) => Seq(cond) ++ invs ++ Seq(body)
      case PLocalVarDecl(idndef, typ, init) => Seq(idndef, typ) ++ (if (init.isDefined) Seq(init.get) else Nil)
      case PFresh(vars) => vars
      case PConstraining(vars, stmt) => vars ++ Seq(stmt)
      case PProgram(file, domains, fields, functions, predicates, methods) =>
        domains ++ fields ++ functions ++ predicates ++ methods
      case PDomain(idndef, typVars, funcs, axioms) => Seq(idndef) ++ typVars ++ funcs ++ axioms
      case PField(idndef, typ) => Seq(idndef, typ)
      case PMethod(idndef, args, rets, pres, posts, body) =>
        Seq(idndef) ++ args ++ rets ++ pres ++ posts ++ Seq(body)
      case PFunction(name, args, typ, pres, posts, body) =>
        Seq(name) ++ args ++ Seq(typ) ++ pres ++ posts ++ body
      case PDomainFunction(name, args, typ, unique) =>
        Seq(name) ++ args ++ Seq(typ)
      case PPredicate(name, args, body) =>
        Seq(name) ++ args ++ body
      case PAxiom(idndef, exp) => Seq(idndef, exp)
      case PTypeVarDecl(name) => Seq(name)
      case PLetWand(idndef, wand) => Seq(idndef, wand)
      case PDefine(idndef, optArgs, exp) => Seq(idndef) ++ optArgs.getOrElse(Nil) ++ Seq(exp)
      case _: PSkip => Nil
    }
  }
}
