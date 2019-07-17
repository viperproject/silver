// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.ast.utility

import viper.silver.ast._

import scala.collection.mutable

/* TODO:
 *   - Removed commented code
 *   - Decompose/tidy up method findNecessaryTypeInstances
 *   - Mark all internal methods as private -> easier for users to find the potentially useful ones
 *   - Add high-level comments describing how the ground instances are computed
 */

object DomainInstances {
  type TypeSubstitution = Map[TypeVar, Type]

  def getInstanceMembers(p: Program, dt: DomainType): (Seq[DomainFunc], Seq[DomainAxiom]) = {
    val domain = p.findDomain(dt.domainName)

    /*      for (a <- domain.axioms){
        var sa = substitute(a, dt.typVarsMap,p)
        var types = collectGroundTypes(sa,p)
        if (!types.subsetOf(p.groundTypeInstances))
          println("")
      }*/
    val functions = domain.functions.map(substitute(_, dt.typVarsMap, p)).filter(collectGroundTypes(_, p).subsetOf(p.groundTypeInstances)).distinct
    val axioms = domain.axioms.map(substitute(_, dt.typVarsMap, p)).filter(collectGroundTypes(_, p).subsetOf(p.groundTypeInstances)).distinct

    (functions, axioms)
  }


  def collectGroundTypes(n: Node, p: Program): Set[Type] = n.deepCollect {
    case t: Type if t.isConcrete => t
    case dfa: DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete) =>
      DomainType(dfa.domainName, dfa.typVarMap)(p.findDomain(dfa.domainName).typVars)
  }.toSet

  ///////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////
  //Generic type instances
  ///////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////
  //Here we calculate all the needed ground instances of generic types (domain and collection types)

  ///////////////////////////////////////////////////////////////////////////////////////////
  //Classes for generic type ground instances
  abstract class GroundTypeInstance

  case class TypeInstance(domain: Domain, arguments: Seq[GroundTypeInstance]) extends GroundTypeInstance

  case class AtomicTypeInstance(t: Type) extends GroundTypeInstance

  case class DomainParameter(d: Domain, tv: TypeVar) {
    assert(d.typVars contains tv)

    override def toString: String = d.name + "[" + tv.name + "]"
  }

  case class DomainParameterDependency(domainParameter: DomainParameter, depth: Int)


  def findNecessaryTypeInstances(p: Program, tcThreshold: Int = 1): Set[Type] = {
    /*
    /*    println("Calculating instance graph")
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
*/
/*sccs
    val g = domains.flatMap { getDomainDependencies(_) }.
      groupBy(_.s).
      map(t => t._1 -> t._2.groupBy(_.t).map(tt => Pair(tt._1, tt._2.map(_.l).toSet))
    )
    val sccs = getSCCs(g)
    val cyclicSCCs = sccs.filter{scc=>scc.exists(dp1=>g(dp1).exists(e=>(scc contains e._1) && e._2.exists{case dt:DomainType => true case _=>false}))}
*/
/*    g.foreach(
      n=>n._2.foreach(
        n2 => println("   " + n._1.toString + " -[" + n2._2.mkString("{",",","}") + "]-> " + n2._1.toString)
      )
    )
*/
/*    if (cyclicSCCs.nonEmpty) {
      println("Potential type cycles found in:")
      cyclicSCCs.foreach {
        scc => println(scc.mkString("{",",","}"))
      }
    }
*/
* */

    /*    val allDFApps union p.deepCollect({
      case dfa : DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete)  => dfa.func(p).
    }).flatten
  */

    val domainFunctionAxiomMap = p.domains.flatMap(d => d.axioms.flatMap(a => a.exp.deepCollect{
      case dfa: DomainFuncApp => dfa -> a
    })).groupBy(pair => pair._1.funcname)

    val allGroundDFAs = p.deepCollect{
      case dfa: DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete) => dfa
    }


    def tryUnify(t1: Type, t2: Type, s: TypeSubstitution): Option[TypeSubstitution] = {
      assert(t2.isConcrete)
      (t1, t2) match {
        case (tv: TypeVar, _) =>
          if (s.contains(tv))
            if (s(tv) == t2)
               Some(s)
            else
              None
          else
            Some(s + (tv -> t2))
        case (gt1: GenericType, gt2: GenericType) =>
          if (gt1.genericName == gt2.genericName)
            tryUnifys(gt1.typeArguments, gt2.typeArguments, s)
          else
            None
        case _ => if (t1 == t2) Some(s) else None
      }
    }

    def tryUnifys(ts1: Seq[Type], ts2: Seq[Type], s: TypeSubstitution): Option[TypeSubstitution] = {
      assert(ts1.size == ts2.size)
      var ss: Option[TypeSubstitution] = Some(s)
      for (tp <- ts1.zip(ts2)) {
        ss match {
          case Some(sss) => ss = tryUnify(tp._1, tp._2, sss)
          case None => return None
        }
      }
      ss
    }

    def tryUnifyWithDefault(tvs: Seq[TypeVar], ts1: Seq[Type], ts2: Seq[Type]): Option[TypeSubstitution] = {
      tryUnifys(ts1, ts2, Map[TypeVar, Type]()) match {
        case Some(s) => Some(complete(s, tvs))
        case None => None
      }
    }
    def complete(ts: TypeSubstitution, tvs: Seq[TypeVar]) =
      (tvs map (tv => tv -> ts.getOrElse(tv, Program.defaultType))).toMap

    val gtis: Set[Type] =
      allGroundDFAs.flatMap(dfa => {
        domainFunctionAxiomMap.get(dfa.funcname) match {
          case Some(ps) =>
            ps.flatMap(f = pair => {
              //            assert(dfa.funcname==pair._1.funcname)
              val d2 = p.findDomain(pair._2.domainName)
              val tvs = d2.typVars
              tryUnifyWithDefault(tvs, tvs.map(pair._1.typVarMap.getOrElse(_, Program.defaultType)), tvs.map(dfa.typVarMap.getOrElse(_, Program.defaultType))) match {
                case Some(ts) => Set[Type](DomainType(pair._2.domainName, ts)(tvs))
                case None => Set[Type]()
              }
            }).toSet
          case None => Set[Type]()
        }
      }).flatMap(downClosureGround).toSet


    var allDirectGroundTypes: Set[Type] = p.deepCollect({
      case t: Type if t.isConcrete => downClosureGround(t)
      case dfa: DomainFuncApp if dfa.typVarMap.values.forall(_.isConcrete) =>
        val d = p.findDomain(dfa.func(p).domainName)
        downClosureGround(DomainType(d, dfa.typVarMap))
    }).flatten.toSet

/*    for (t <- gtis)
      if (!allDirectGroundTypes.contains(t))
        println(t.toString())
*/
    allDirectGroundTypes = allDirectGroundTypes.union(gtis)

    val todo = new mutable.Queue[TypeCoordinate]()
    val done = new mutable.HashSet[TypeCoordinate]()
    val tcLuggage = new mutable.HashMap[TypeCoordinate, Map[TypeVar, Int]]()

    //    val baseTCs = new mutable.HashSet[TypeCoordinate]()
    for (gt <- allDirectGroundTypes) {
      val tc = makeTypeCoordinate(gt)
      recursiveBottomUpEnqueue(todo, done, tc)
      if (!(tcLuggage contains tc)) {
        tcLuggage(tc) = gt match {
          case dt: DomainType => dt.typeParameters.map (_ -> 0).toMap
          case _ => Map()
        }
      }
    }

    def recursiveBottomUpEnqueue(todo: mutable.Queue[TypeCoordinate], done: mutable.HashSet[TypeCoordinate], tc: TypeCoordinate): Unit = {
      if (done add tc) {
        assert(!(todo contains tc))
        for (stc <- tc.subTCs)
          if (!(todo contains stc))
            recursiveBottomUpEnqueue(todo, done, stc)
        assert(!(todo contains tc))
        todo.enqueue(tc)
      }
    }



    //    var newTCs : mutable.Set[TypeCoordinate] = Set()


    while (todo.nonEmpty) {
      val tc = todo.dequeue()
      assert(done contains tc)
      assert(tcLuggage contains tc)
//      println("   Adding type coordinate <" + tc.toString() + ">")
      val ntcs = new mutable.HashSet[TypeCoordinate]()
      tc match {
        /*        case ctc : CollectionTypeCoordinate =>
          val tc2 = ctc.etc
          ntcs += tc2
          tcLuggage(tc2)=Map()*/
        case _: AtomicTypeCoordinate =>
        case gitc@GenericInstanceTypeCoordinate(_, typeArgs) =>
          assert(typeArgs.forall { tc => done contains tc })
          val types = gitc.collectTypes(p)
          types.foreach(t => {
            val tc2 = makeTypeCoordinate(t.substitute(gitc.typeSubstitution))
            if (!(done contains tc2)) {
              val tc2InflationMap =
                (t match {
                  case dt2: DomainType =>
                    dt2.typVarsMap.map {
                      case (tv2: TypeVar, t2: Type) =>
                        tv2 -> (getFTVDepths(t2).map { case (ftv: TypeVar, d: Int) => d + tcLuggage(tc)(ftv) } ++ Seq(0)).max
                    }
                  case _ => Seq()
                }).toMap

              if (tc2InflationMap.values.forall(_ <= tcThreshold)) {
                if (!tcLuggage.contains(tc2))
                  tcLuggage(tc2) = tc2InflationMap
                else
                  tcLuggage(tc2) = (
                       tcLuggage(tc2)
                    ++ tc2InflationMap.map { case (tv, d) => tv -> (d + tcLuggage(tc2).getOrElse(tv, 0)) })

                assert(tcLuggage contains tc2)
                ntcs += tc2
              }
            }
        })
      }

      for (ntc <- ntcs) {
        assert(ntc.subTCs.forall(tc=>(done union ntcs).contains(tc)))
        recursiveBottomUpEnqueue(todo, done, ntc)
      }

      /*
      ntcs.foreach {
        tc2 =>{
          assert (tcLuggage contains tc2)
          done add tc2
          todo.enqueue(tc2)
        }
      }
  */
    }

//    println("Calculating ground type instances done - total " + done.size)
    val result = done.map(_.t).toSet
//    println("Calculating ground type instances result done - total " + result.size)

    result
  }

  def substitute[A <: Node](e: A, s: TypeSubstitution, p: Program): A =
    e.transform {
      case dfa@DomainFuncApp(_, args, ts) =>
        val ts2 = ts.toSeq.map(pair => (pair._1, substitute(pair._2, s, p))).toMap
        val argss = args map (substitute(_, s, p))
        DomainFuncApp(dfa.func(p), argss, ts2)(dfa.pos, dfa.info)
      //            )(dfa.pos, dfa.info, substitute(dfa.typ,s), dfa.formalArgs.map(substitute(_,s)))
      case lvd@LocalVar(name, _) =>
        LocalVar(name, substitute(lvd.typ, s, p))(lvd.pos, lvd.info)

      case t: Type =>
        t.substitute(s)
    }

  def showInstanceMembers(p: Program): Unit = {
    println("================== Domain instances")
    for (ti <- p.groundTypeInstances) {
      ti match {
        case dt: DomainType =>
          println("Members for Domain type " + dt.toString())
          val domain = p.findDomain(dt.domainName)
          val (fs, as) = getInstanceMembers(p, dt)
          //          val sfs = domain.functions.map(substitute(_,dt.typVarsMap,p))
          for (f <- fs)
            println("   " + f.toString())
          for (a <- as)
            println("   " + a.toString())
          for (rf <- domain.functions.filter(f => fs.forall((ff) => ff.name != f.name)))
            println("   Rejected " + substitute(rf, dt.typVarsMap, p).toString())
          for (ra <- domain.axioms.filter(a => as.forall((aa) => aa.name != a.name)))
            println("   Rejected " + substitute(ra, dt.typVarsMap, p).toString())
      case _ =>
      }
    }
    println("================== Domain instances done")
    val allTypes = collectGroundTypes(p,p)
    for (t <- allTypes)
      println(t.toString())
  }

  def getFTVDepths(t: Type): Map[TypeVar, Int] = t match {
    case dt: DomainType =>
      dt.typVarsMap.flatMap {
        case (tv: TypeVar, t: Type) => getFTVDepths(t).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }
      }
    case ct: CollectionType => getFTVDepths(ct.elementType).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }
    case tv: TypeVar => Map(tv -> 0)
    case at: BuiltInType => Map()
  }


  def down1Types(t: Type): Set[Type] = t match {
    case dt: DomainType => dt.typVarsMap.values.toSet
    case ct: CollectionType => Set(ct.elementType)
    case _: BuiltInType => Set()
    case _: TypeVar => Set()
  }

  def downClosure(t: Type): Set[Type] =
  /*(if (t.isConcrete) Set(t) else  Set())*/ Set(t) ++ down1Types(t).flatMap(downClosure)

  def downClosureGround(t: Type): Set[Type] =
    (if (t.isConcrete) Set(t) else Set()) ++ down1Types(t).flatMap(downClosure)


  def collectDomainTypes(n: Node, p: Program): Set[Type] ={
  //    d.deepCollect{case t : Type => downClosure(t)}.flatten.toSet
    n.shallowCollect {
      case t: Type =>
        downClosure(t)
      case dfa@DomainFuncApp(_, args, typVarMap) =>
        /* Given a domain function application, we collect the following types:
         *   - return type of the function application
         *   - domain that the applied function belongs to
         *   - from the provided function arguments
         *   - from the type variable map used for the application
         */
        val d = p.findDomain(dfa.domainName)
        val m = d.typVars.map(t => t -> dfa.typVarMap.getOrElse(t, Program.defaultType)).toMap
        val dt = DomainType(d, m)

        (   Set(dfa.typ, dt)
         ++ (args flatMap (collectDomainTypes(_, p)))
         ++ (typVarMap.values flatMap (collectDomainTypes(_,p))))
    }.flatten.toSet
  }

  //////////////////////////////////////////////////////////////////////////////////////
  //Type Coordinates
  //A type coordinate is

  def makeTypeCoordinate(t: Type): TypeCoordinate = t match {
    case ct: CollectionType => new CollectionTypeCoordinate(ct,makeTypeCoordinate(ct.elementType))
    case bit: BuiltInType => AtomicTypeCoordinate(bit)
    case dt: DomainType => new DomainInstanceTypeCoordinate(dt,
      dt.typeParameters.map(tv => makeTypeCoordinate(dt.typVarsMap(tv)))
    )
    case tv:TypeVar => throw new Exception("Internal error in type system - unexpected non-ground type <" + t.toString() + ">")
  }

  sealed abstract class TypeCoordinate(val t: Type) {
    def subTCs: Set[TypeCoordinate]

    require(t.isConcrete)
    override def toString: String = t.toString()
//    def down: Set[TypeCoordinate]
  }

  sealed class CollectionClass

  object CollectionClass extends Enumeration {
    type CollectionClass = Value
    val Seq,Set,Multiset = Value

    def makeCT(cc: CollectionClass,et: Type): CollectionType = cc match{
      case Set => SetType(et)
      case Seq => SeqType(et)
      case Multiset => MultisetType(et)
    }

    def getCC(ct: CollectionType): CollectionClass.Value =
    {
      ct match {
        case SetType(_) => Set
        case MultisetType(_) => Multiset
        case SeqType(_) => Seq
      }
    }

    def ccName(cc:CollectionClass): String =
      cc match {
        case Set => "Set"
        case Multiset => "Multiset"
        case Seq => "Seq"
      }
  }

  sealed case class AtomicTypeCoordinate(bit: BuiltInType) extends TypeCoordinate(bit){
    override def subTCs = Set()
//    override def down: Set[TypeCoordinate] = Set(this)
  }
  abstract sealed case class GenericInstanceTypeCoordinate(gname: String, args: Seq[TypeCoordinate])(val gt: GenericType)
    extends TypeCoordinate(gt){
    def typeSubstitution: Map[TypeVar, Type]
    override def subTCs: Set[TypeCoordinate] = args.toSet

    //    override def down: Set[TypeCoordinate] = Set(this) ++ args.flatMap(_.down)
    def collectTypes(p: Program): Set[Type]
  }
  sealed class CollectionTypeCoordinate(ct: CollectionType, etc: TypeCoordinate)
    extends GenericInstanceTypeCoordinate(CollectionClass.ccName(CollectionClass.getCC(ct)),Seq(etc))(ct){
    val cc: CollectionClass.Value = CollectionClass.getCC(ct)
    override def collectTypes(p: Program) = Set()
    override def typeSubstitution = Map()
  }
  sealed class DomainInstanceTypeCoordinate(val dt: DomainType, typeArgs: Seq[TypeCoordinate])
    extends GenericInstanceTypeCoordinate(dt.domainName, typeArgs)(dt){
    override def collectTypes(p: Program): Set[Type] = {
      val domain = p.findDomain(dt.domainName)
      collectDomainTypes(domain, p)
    }
    override def typeSubstitution: Map[TypeVar, Type] = dt.typVarsMap
//    val typeArguments = dt.typeArguments
  }


  case class TarjanNode[N](n: N, var es: Array[TarjanNode[N]], var index: Int, var lowIndex: Int)

  class TarjanAR[N](val nodes: Map[N,TarjanNode[N]]) {
    val r = new mutable.ListBuffer[mutable.Set[N]]()
    var index: Int = 0
    var stack = List.empty[N]
    val set = new mutable.HashSet[N]()
  }
/*  def getSCCs[N, L](g: Map[N, Map[N, L]]): List[mutable.Set[N]] = {
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
      var ns = new mutable.HashSet[N]
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

  def getDomainDependencies(p:Program,d:Domain) : Set[DPEdge] =
    getDomainTypeInstances(d).flatMap{
      case dt2 : DomainType => dt2.typVarsMap.flatMap{
        case (tv2:TypeVar,tv:TypeVar) => Seq(DPEdge(DomainParameter(d,tv), tv, DomainParameter(p.findDomain(dt2.domainName),tv2)))
        case (tv2:TypeVar,dt3:DomainType) => getTVs(dt3).flatMap{
          tv=>Seq(DPEdge(DomainParameter(d, tv), dt3, DomainParameter(p.findDomain(dt2.domainName), tv2)))
        }
        case _ => Seq()
      }
      case _ => Seq()
    }
             */
  def getTVs(t: Type): Set[TypeVar] =
    t match {
      case tv: TypeVar => Set(tv)
      case dt: DomainType =>
        (dt.typeParameters.toSet -- dt.typVarsMap.keys) ++ dt.typVarsMap.values.flatMap(getTVs)
      case ct: CollectionType => getTVs(ct.elementType)
      case _ => Set()
    }

  def getDomainTypeInstances(d: Domain): Set[Type] =
    d.deepCollect { case t: Type => t }.toSet

  ///////////////////////////////////////////////////////////////////////////////////////////
  //End generic type instances
  ///////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////

}
