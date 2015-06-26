/*
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
 */

package viper.silver.ast

//import sun.org.mozilla.javascript.internal.ast.AstNode
import utility.{Consistency, Types}
import org.kiama.output._

import scala.collection.immutable.HashSet
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

/** A Silver program. */
case class Program(domains: Seq[Domain], fields: Seq[Field], functions: Seq[Function], predicates: Seq[Predicate], methods: Seq[Method])
                  (val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed {
  require(
    Consistency.noDuplicates(
      (members map (_.name)) ++
        (domains flatMap (d => (d.axioms map (_.name)) ++ (d.functions map (_.name))))
    ), "names of members must be distinct"
  )

  val groundTypeInstances = findNecessaryTypeInstances()

  lazy val members = domains ++ fields ++ functions ++ predicates ++ methods

  def findField(name: String): Field = {
    this.fields.find(_.name == name) match {
      case Some(f) => f
      case None => sys.error("Field name " + name + " not found in program.")
    }
  }

  def findMethod(name: String): Method = {
    this.methods.find(_.name == name) match {
      case Some(m) => m
      case None => sys.error("Method name " + name + " not found in program.")
    }
  }

  def findFunction(name: String): Function = {
    this.functions.find(_.name == name) match {
      case Some(f) => f
      case None => sys.error("Function name " + name + " not found in program.")
    }
  }

  def findPredicate(name: String): Predicate = {
    this.predicates.find(_.name == name) match {
      case Some(p) => p
      case None => sys.error("Predicate name " + name + " not found in program.")
    }
  }

  def findDomain(name: String): Domain = {
    this.domains.find(_.name == name) match {
      case Some(d) => d
      case None => sys.error("Domain name " + name + " not found in program.")
    }
  }

  def findDomainFunction(name: String): DomainFunc = {
    this.domains.flatMap(_.functions).find(_.name == name) match {
      case Some(f) => f
      case None => sys.error("Domain function " + name + " not found in program.")
    }

  }

  case class DomainArg(domain: Domain, i: Int)

  abstract class GroundTypeInstance()

  case class TypeInstance(domain: Domain, arguments: Seq[GroundTypeInstance]) extends GroundTypeInstance

  case class AtomicTypeInstance(t: Type) extends GroundTypeInstance

  //class GroundCollectionType : GroundType
  case class DomainParameter(d: Domain, tv: TypeVar) {
    assert(d.typVars contains tv)
    override def toString : String = d.name + "[" + tv.name + "]"
  }

  case class DomainParameterDependency( domainParameter: DomainParameter, depth: Int)


  def findNecessaryTypeInstances(): Map[Domain, Set[GroundTypeInstance]] = {
    val result = new scala.collection.immutable.ListMap[Domain, Set[GroundTypeInstance]]()

    println("Calculating instance graph")
    println("  Domains:")
    domains.foreach(
      d=>{
        println("    " + d.name + "[" + d.typVars.mkString(",") + "]")
        getDomainTypeInstances(d).foreach(
          t => println("      " + t.toString())
        )
      }
    )

    println("  Dependency edges:")
      domains.flatMap{getDomainDependencies(_)}.foreach(
        e => println("    " + e.s.toString + " -> " +e.t.toString)
      )

    val g = domains.flatMap { getDomainDependencies(_) }. //
      groupBy(_.s).
      map(t => t._1 -> t._2.groupBy(_.t).map(tt => Pair(tt._1, tt._2.map(_.l).toSet))
    )

    g.foreach(
      n=>n._2.foreach(
        n2 => println("   " + n._1.toString + " -[" + n2._2.mkString("{",",","}") + "]-> " + n2._1.toString)
      )
    )

    val sccs = getSCCs(g)
    var cyclicSCCs = sccs.filter{scc=>scc.exists(dp1=>g(dp1).exists(e=>(scc contains e._1) && e._2.exists{case dt:DomainType => true case _=>false}))}
    if (cyclicSCCs.nonEmpty) {
      println("Potential type cycles found in:")
      cyclicSCCs.foreach {
        scc => println(scc.mkString("{",",","}"))
      }
    }

    
    val allDirectGroundTypes = deepCollect({
      case t : Type if t.isConcrete => t
    })
    
    val allDirectGroundInstances = allDirectGroundTypes.filter { case dt : DomainType  => true case _ => false }
    
    val todo = new collection.mutable.Queue[TypeCoordinate]()
    val done = new collection.mutable.HashSet[TypeCoordinate]()
    
    allDirectGroundTypes.foreach(
      gt=>{
        val tc = makeTypeCoordinate(gt)
        if (done add tc)
          todo.enqueue(tc)
      }
    )
    
    while (todo.nonEmpty)
    {
      val tc = todo.dequeue()
      assert (done contains tc)
      println("   Adding type coordinate <" + tc.toString() + ">")
      for (tc2 <- getTCSTCs(tc))
          if (done add tc2)
            todo.enqueue(tc2)
    }
      
    println("Calculating ground type instances done")
    result
  }

  def getTCSTCs(tc:TypeCoordinate) : Set[TypeCoordinate] =       
    tc match{
        case at : AtomicTypeCoordinate => Set()
        case ditc : DomainInstanceTypeCoordinate =>
          (getTypes(findDomain(ditc.dn)).map(tt=>makeTypeCoordinate(tt.substitute(ditc.dt.typVarsMap))) ++ ditc.args)
        case ctc : CollectionTypeCoordinate =>
          Set(makeTypeCoordinate(ctc.et))
    }

  def getTypes(d:Domain) : Set[Type] = d.deepCollect{case t : Type => t}.toSet
  
  def makeTypeCoordinate(t:Type) : TypeCoordinate = 
    t match {
    case ct  : CollectionType => CollectionTypeCoordinate(CollectionClass.getCC(ct),ct.elementType)
    case bit : BuiltInType    => AtomicTypeCoordinate(bit)
    case dt  : DomainType     => new DomainInstanceTypeCoordinate(
        dt.domainName,
        dt.domainTypVars.map(tv=>makeTypeCoordinate(dt.typVarsMap(tv))).toSeq
        )(dt)
    case tv:TypeVar => throw new Exception("Internal error in type system - unexpected non-ground type <" + t.toString() + ">")
  }
  sealed abstract class TypeCoordinate(val t : Type){
    require(t.isConcrete)
    override def toString = t.toString()
  }
  
  class CollectionClass
  object CollectionClass extends Enumeration{
    type CollectionClass = Value
    val Seq,Set,MultiSet = Value
    
    def makeCT(cc : CollectionClass,et:Type) = cc match{
      case Set => SetType(et)
      case Seq => SeqType(et)
      case MultiSet => MultisetType(et)
    }
    
    def getCC(ct : CollectionType) : CollectionClass.Value =
    {
      ct match {
        case SetType(_) => Set
        case MultisetType(_) => MultiSet
        case SeqType(_) => Seq
      }
    }
    
  }
  
   
  case class AtomicTypeCoordinate(bit : BuiltInType) extends TypeCoordinate(bit)
  case class CollectionTypeCoordinate(cc : CollectionClass.Value, et : Type) extends TypeCoordinate(CollectionClass.makeCT(cc, et))
  case class DomainInstanceTypeCoordinate(dn : String,args:Seq[TypeCoordinate])(val dt:DomainType) extends TypeCoordinate(dt)
 
  
  case class TarjanNode[N](n:N,var es:Array[TarjanNode[N]],var index:Int,var lowIndex:Int)
  class TarjanAR[N](val nodes:Map[N,TarjanNode[N]])
  {
    val r = new scala.collection.mutable.ListBuffer[Set[N]]()
    var index : Int = 0
    val stack = new scala.collection.mutable.Stack[N]()
    val set = new scala.collection.mutable.HashSet[N]()
  }
  def getSCCs[N, L](g: Map[N, Map[N, L]]): List[Set[N]] = {
    val tNodes = g.map { e => e._1 -> TarjanNode(e._1, null, -1, 0) }
    tNodes.values.foreach(n=>{n.es=g(n.n).keys.map(tNodes(_)).toArray})
    val ar = new TarjanAR[N](tNodes)
    for (n <- tNodes.values) {
      if (n.index == -1) {
        sccr(ar,n)
      }
    }
    ar.r.toList
  }
  def sccr[N](ar:TarjanAR[N],n: TarjanNode[N]) :Unit =
  {
    n.index = ar.index
    n.lowIndex = ar.index
    ar.index+=1
    // Set the depth index for v to the smallest unused index
    ar.stack.push(n.n)
    ar.set += n.n

    for (sn <- n.es)
    {
      if (sn.index== -1)
      {
        sccr(ar,sn)
        if (sn.lowIndex < n.lowIndex)
          n.lowIndex = sn.lowIndex
      }else if (ar.set contains sn.n){
          if (sn.index < n.lowIndex)
            n.lowIndex = sn.index
      }
    }
    if (n.index==n.lowIndex)
    {
      assert (ar.set.nonEmpty)
      assert (ar.set contains n.n)
      var ns = new HashSet[N]
      var u = ar.stack.top
      do{
        u = ar.stack.pop()
        ar.set.remove(u)
        ns += u
      } while ( u!=n.n)
      ar.r += ns
    }
  }

  case class DPEdge(s: DomainParameter,l:Type,t:DomainParameter )

  def getDomainDependencies(d:Domain) : Set[DPEdge] =
  getDomainTypeInstances(d).flatMap{
    case dt2 : DomainType => dt2.typVarsMap.flatMap{
      case (tv2:TypeVar,tv:TypeVar) => Seq(DPEdge(DomainParameter(d,tv), tv, DomainParameter(findDomain(dt2.domainName),tv2)))
      case (tv2:TypeVar,dt3:DomainType) => getTVs(dt3).flatMap{
        tv=>Seq(DPEdge(DomainParameter(d, tv), dt3, DomainParameter(findDomain(dt2.domainName), tv2)))
      }
      case _ => Seq()
    }
    case _ => Seq()
  }
/*    val r = new ListBuffer[DPEdge]()
    println("=2:" + d.name )
    for (t <- getDomainTypeInstances(d)) {
      println("==3:" + d.name + " : " + t.toString())
      t match {
        case dt2: DomainType => {
          println("===4: " + dt2.domainName + "[" + dt2.typVarsMap.mkString(",") + "]")
          for (kv <- dt2.typVarsMap) {
            println("====5: " + kv.toString())
            kv._2 match {
              case tv: TypeVar => {
                r += DPEdge(DomainParameter(d, tv), kv._2, DomainParameter(findDomain(dt2.domainName), kv._1))
                println("++++++ " + r.last.toString)
              }
              case dt3: DomainType => {
                println("=====6: " + dt3.toString())
//                for (kv3 <- dt3.typVarsMap) {
  //                println("******7: " + kv3._2)
                  val s = getTVs(dt3) //deepCollect{case tv : TypeVar => tv}
                  for (tv <- s){ //kv3._2.typeVariables) {
                    println("======7:  " + tv.name)
                    r += DPEdge(DomainParameter(d, tv), kv._2, DomainParameter(findDomain(dt2.domainName), kv._1))
                    println("++++++ " + r.last.toString)
                  }
//                }
              }
              case _ => {}
            }
          }
        }
        case _ => {}
      }
    }
    r.toSet
  }
  */
  def getTVs(t:Type) : Set[TypeVar] =
    t match {
      case tv : TypeVar => Set(tv)
      case dt : DomainType =>
        ((dt.domainTypVars.toSet -- dt.typVarsMap.keys) ++ dt.typVarsMap.values.flatMap(getTVs(_)))
      case ct : CollectionType => getTVs(ct.elementType)
      case _ => Set()
    }




/*    getDomainTypeInstances(d).flatMap {
      case d2t: DomainType =>
        //  if !d2t.isConcrete =>
        d2t.typVarsMap.flatMap {
          case ((tv2 : TypeVar,t3:Type)) => t3 match {
                  case tv : TypeVar =>
                    Seq(DPEdge(DomainParameter(d, tv), tv2, DomainParameter(findDomain(d2t.domainName), tv2)))
                case d3: DomainType => d3.typeVariables.map {
                  case tv =>
                    DPEdge(DomainParameter(d, tv), tv2, DomainParameter(findDomain(d2t.domainName), tv2))
                }
          }
          case _ => Seq()
      }
      case _ => Seq()
      }
  */
  def getDomainTypeInstances(d:Domain) : Set[Type] =
    d.deepCollect {
      case t: Type => t
    }.toSet

}//class Program


// --- Program members

/** A field declaration. */
case class Field(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Location with Typed {
  require(typ.isConcrete, "Type of field " + name + ":" + typ + " must be concrete!")
}

/** A predicate declaration. */
case class Predicate(name: String, formalArgs: Seq[LocalVarDecl], private var _body: Option[Exp])(val pos: Position = NoPosition, val info: Info = NoInfo) extends Location {
  if (body != null) body map Consistency.checkNonPostContract
  def body = _body
  def body_=(b: Option[Exp]) {
    b map Consistency.checkNonPostContract
    _body = b
  }
  def isAbstract = body.isEmpty
}

/** A method declaration. */
case class Method(name: String, formalArgs: Seq[LocalVarDecl], formalReturns: Seq[LocalVarDecl], private var _pres: Seq[Exp], private var _posts: Seq[Exp], private var _locals: Seq[LocalVarDecl], private var _body: Stmt)
                 (val pos: Position = NoPosition, val info: Info = NoInfo) extends Member with Callable with Contracted {
  if (_pres != null) _pres foreach Consistency.checkNonPostContract
  if (_posts != null) _posts foreach Consistency.checkPost
  if (_body != null) Consistency.checkNoArgsReassigned(formalArgs, _body)
  require(noDuplicates)
  require((formalArgs ++ formalReturns) forall (_.typ.isConcrete))
  private def noDuplicates = Consistency.noDuplicates(formalArgs ++ Consistency.nullValue(locals, Nil) ++ Seq(LocalVar(name)(Bool)))
  def pres = _pres
  def pres_=(s: Seq[Exp]) {
    s foreach Consistency.checkNonPostContract
    _pres = s
  }
  def posts = _posts
  def posts_=(s: Seq[Exp]) {
    require(s forall Consistency.noResult)
    s foreach Consistency.checkPost
    _posts = s
  }
  def locals = _locals
  def locals_=(s: Seq[LocalVarDecl]) {
    _locals = s
    require(noDuplicates)
  }
  def body = _body
  def body_=(b: Stmt) {
    Consistency.checkNoArgsReassigned(formalArgs, b)
    _body = b
  }
}

/** A function declaration */
case class Function(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, private var _pres: Seq[Exp], private var _posts: Seq[Exp], private var _body: Option[Exp])
                   (val pos: Position = NoPosition, val info: Info = NoInfo) extends Member with FuncLike with Contracted {
  require(_posts == null || (_posts forall Consistency.noOld))
  require(_body == null || (_body map (_ isSubtype typ) getOrElse true))
  if (_pres != null) _pres foreach Consistency.checkNonPostContract
  if (_posts != null) _posts foreach Consistency.checkPost
  if (_body != null) _body map Consistency.checkFunctionBody
  def pres = _pres
  def pres_=(s: Seq[Exp]) {
    s foreach Consistency.checkNonPostContract
    _pres = s
  }
  def posts = _posts
  def posts_=(s: Seq[Exp]) {
    require(s forall Consistency.noOld)
    s foreach Consistency.checkPost
    _posts = s
  }
  def body = _body
  def body_=(b: Option[Exp]) {
    require(b map (_ isSubtype typ) getOrElse true)
    b map Consistency.checkFunctionBody
    _body = b
  }

  /**
   * The result variable of this function (without position or info).
   */
  def result = Result()(typ)

  /**
   * Is this function recursive?
   */
  def isRecursive: Boolean = body exists (_ existsDefined {
    case FuncApp(funcname, _) if name == funcname =>
  })

  def isAbstract = body.isEmpty
}


// --- Local variable declarations

/**
 * Local variable declaration.  Note that these are not statements in the AST, but
 * rather occur as part of a method, loop, function, etc.
 */
case class LocalVarDecl(name: String, typ: Type)(val pos: Position = NoPosition, val info: Info = NoInfo) extends Node with Positioned with Infoed with Typed {
  require(Consistency.validUserDefinedIdentifier(name))

  /**
   * Returns a local variable with equivalent information
   */
  lazy val localVar = LocalVar(name)(typ, pos, info)
}


// --- Domains and domain members

/** A user-defined domain. */
case class Domain(name: String, var _functions: Seq[DomainFunc], var _axioms: Seq[DomainAxiom], typVars: Seq[TypeVar] = Nil)
                 (val pos: Position = NoPosition, val info: Info = NoInfo) extends Member with Positioned with Infoed {
  require(Consistency.validUserDefinedIdentifier(name))
  def functions = _functions
  def functions_=(fs: Seq[DomainFunc]) {
    _functions = fs
  }
  def axioms = _axioms
  def axioms_=(as: Seq[DomainAxiom]) {
    _axioms = as
  }
}

/** A domain axiom. */
case class DomainAxiom(name: String, exp: Exp)(val pos: Position = NoPosition, val info: Info = NoInfo) extends DomainMember {
  require(Consistency.noResult(exp), "Axioms can never contain result variables.")
  require(Consistency.noOld(exp), "Axioms can never contain old expressions.")
  require(Consistency.noAccessLocation(exp), "Axioms can never contain access locations.")
  require(exp isSubtype Bool)
  Consistency.checkNoPositiveOnly(exp)
}

/** Domain function which is not a binary or unary operator. */
case class DomainFunc(name: String, formalArgs: Seq[LocalVarDecl], typ: Type, unique: Boolean = false)
                     (val pos: Position = NoPosition, val info: Info = NoInfo) extends AbstractDomainFunc with DomainMember {
  require(!unique || formalArgs.isEmpty, "Only constants, i.e. nullary domain functions can be unique.")
}


// --- Common functionality

/** Common ancestor for members of a program. */
sealed trait Member extends Node with Positioned with Infoed {
  require(Consistency.validUserDefinedIdentifier(name))
  def name: String

  // we override the definition of hashCode/equals to avoid unbounded recursion
  override def hashCode = name.hashCode
  override def equals(o: Any) = o match {
    case m: Member => name == m.name
    case _ => false
  }
}

/** Common ancestor for domain members. */
sealed trait DomainMember extends Node with Positioned with Infoed {
  require(Consistency.validUserDefinedIdentifier(name))

  def name: String

  /** See [[viper.silver.ast.utility.Types.freeTypeVariables]]. */
  lazy val freeTypeVariables = Types.freeTypeVariables(this)

  // we override the definition of hashCode/equals to avoid unbounded recursion
  override def hashCode = name.hashCode

  override def equals(o: Any) = o match {
    case m: DomainMember => name == m.name
    case _ => false
  }
}

/** Common ancestor for things with formal arguments. */
sealed trait Callable {
  require(Consistency.noDuplicates(formalArgs))
  def formalArgs: Seq[LocalVarDecl]
  def name: String
}

/** Common ancestor for functions and domain functions */
sealed trait FuncLike extends Callable with Typed

/** A member with a contract. */
sealed trait Contracted extends Member {
  if (pres != null) pres map Consistency.checkNonPostContract
  if (posts != null) posts map Consistency.checkPost
  def pres: Seq[Exp]
  def posts: Seq[Exp]
}

/** A common trait for locations (fields and predicates). */
sealed trait Location extends Member

/** Common superclass for domain functions and binary/unary operators. */
sealed trait AbstractDomainFunc extends FuncLike with Positioned with Infoed


// --- Built-in domain functions and operators

/** Built-in domain functions  */
sealed trait BuiltinDomainFunc extends AbstractDomainFunc {
  lazy val info = NoInfo
  lazy val pos = NoPosition
}

/** Domain functions which are written as infix or prefix operators. */
sealed trait Op extends AbstractDomainFunc with BuiltinDomainFunc {
  lazy val name = op
  def op: String
  def fixity: Fixity
  def priority: Int
}

/** Domain functions with return type integer. */
sealed trait IntDomainFunc extends AbstractDomainFunc {
  lazy val typ = Int
}
/** Domain functions with return type boolean. */
sealed trait BoolDomainFunc extends AbstractDomainFunc {
  lazy val typ = Bool
}
/** Domain functions with return type permission. */
sealed trait PermDomainFunc extends AbstractDomainFunc {
  lazy val typ = Perm
}

/** Domain functions that represent built-in binary operators */
sealed trait BinOp extends Op {
  lazy val formalArgs = List(LocalVarDecl("left", leftTyp)(), LocalVarDecl("right", rightTyp)())
  def leftTyp: Type
  def rightTyp: Type
}

/** Left associative operator. */
sealed trait LeftAssoc {
  lazy val fixity = Infix(LeftAssoc)
}

/** Domain functions that represent built-in binary operators where both arguments are integers. */
sealed trait IntBinOp extends BinOp {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Domain functions that represent built-in binary operators where both arguments are booleans. */
sealed trait BoolBinOp extends BinOp {
  lazy val leftTyp = Bool
  lazy val rightTyp = Bool
}

/** Domain functions that represent built-in binary operators where both arguments are permissions. */
sealed trait PermBinOp extends BinOp {
  lazy val leftTyp = Perm
  lazy val rightTyp = Perm
}

/** Domain functions that represent built-in unary operators */
sealed trait UnOp extends Op {
  lazy val formalArgs = List(LocalVarDecl("exp", expTyp)())
  def expTyp: Type
}

/** Common interface for sum operators. */
sealed abstract class SumOp(val op: String) extends LeftAssoc {
  lazy val priority = 12
}
/** Common interface for product operators. */
sealed abstract class ProdOp(val op: String) extends LeftAssoc {
  lazy val priority = 11
}
/** Common interface for relational operators. */
sealed abstract class RelOp(val op: String) extends BoolDomainFunc {
  lazy val priority = 13
  lazy val fixity = Infix(NonAssoc)
}

// Arithmetic integer operators
case object AddOp extends SumOp("+") with IntBinOp with IntDomainFunc
case object SubOp extends SumOp("-") with IntBinOp with IntDomainFunc
case object MulOp extends ProdOp("*") with IntBinOp with IntDomainFunc
case object DivOp extends ProdOp("\\") with IntBinOp with IntDomainFunc
case object ModOp extends ProdOp("%") with IntBinOp with IntDomainFunc

// Arithmetic permission operators
case object PermAddOp extends SumOp("+") with PermBinOp with PermDomainFunc
case object PermSubOp extends SumOp("-") with PermBinOp with PermDomainFunc
case object PermMulOp extends ProdOp("*") with PermBinOp with PermDomainFunc
case object IntPermMulOp extends ProdOp("*") with BinOp with PermDomainFunc {
  lazy val leftTyp = Int
  lazy val rightTyp = Perm
}
case object PermDivOp extends ProdOp("/") with BinOp with PermDomainFunc {
  lazy val leftTyp = Perm
  lazy val rightTyp = Int
}
case object FracOp extends ProdOp("/") with BinOp with PermDomainFunc {
  lazy val leftTyp = Int
  lazy val rightTyp = Int
}

/** Integer negation. */
case object NegOp extends UnOp with IntDomainFunc {
  lazy val expTyp = Int
  lazy val op = "-"
  lazy val priority = 10
  lazy val fixity = Prefix
}

// Integer comparison operators
case object LtOp extends RelOp("<") with IntBinOp
case object LeOp extends RelOp("<=") with IntBinOp
case object GtOp extends RelOp(">") with IntBinOp
case object GeOp extends RelOp(">=") with IntBinOp

// Permission comparison operators
case object PermLtOp extends RelOp("<") with PermBinOp
case object PermLeOp extends RelOp("<=") with PermBinOp
case object PermGtOp extends RelOp(">") with PermBinOp
case object PermGeOp extends RelOp(">=") with PermBinOp

/** Boolean or. */
case object OrOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "||"
  lazy val priority = 3
}

/** Boolean and. */
case object AndOp extends BoolBinOp with BoolDomainFunc with LeftAssoc {
  lazy val op = "&&"
  lazy val priority = 2
}

/** Boolean implication. */
case object ImpliesOp extends BoolBinOp with BoolDomainFunc {
  lazy val op = "==>"
  lazy val priority = 4
  lazy val fixity = Infix(RightAssoc)
}

/** Boolean negation. */
case object NotOp extends UnOp with BoolDomainFunc {
  lazy val expTyp = Bool
  lazy val op = "!"
  lazy val priority = 1
  lazy val fixity = Prefix
}
