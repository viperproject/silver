package viper.silver.ast.utility

import viper.silver.ast._

import scala.collection.mutable

/**
  * Created by juhaszu on 11-Feb-16.
  */
object DomainInstances {
  type TypeSubstitution = Map[TypeVar,Type]

  def substitute[A<:Node](e:A,s:TypeSubstitution) : A =
    Transformer.transform[A](e,{case gt:GenericType => gt.substitute(s)})()

  def collectTypes(n:Node) = n.deepCollect({case t : Type => t}).toSet
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
    override def toString : String = d.name + "[" + tv.name + "]"
  }

  case class DomainParameterDependency( domainParameter: DomainParameter, depth: Int)


  def findNecessaryTypeInstances(p : Program,tcThreshold : Int = 1): Set[Type] = {
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
    val allDirectGroundTypes = p.deepCollect({
      case t : Type if t.isConcrete => downClosure(t)
    }).flatten

    val todo = new mutable.Queue[TypeCoordinate]()
    val done = new mutable.HashSet[TypeCoordinate]()
    val tcLuggage = new mutable.HashMap[TypeCoordinate,Map[TypeVar,Int]]()

    val baseTCs = new mutable.HashSet[TypeCoordinate]()
    allDirectGroundTypes.foreach(
      gt=>{
        val tc = makeTypeCoordinate(gt)
        baseTCs += tc
        if (done add tc)
        {
          todo.enqueue(tc)
          tcLuggage(tc)= gt match{
            case dt:DomainType => dt.typeParameters.map{ v => v -> 0}.toMap
            case _ => Map()
          }
        }
      }
    )



    while (todo.nonEmpty)
    {
      val tc = todo.dequeue()
      assert (done contains tc)
      assert (tcLuggage contains  tc)
//      println("   Adding type coordinate <" + tc.toString() + ">")
      val ntcs = new mutable.HashSet[TypeCoordinate]()
      tc match{
        case ctc : CollectionTypeCoordinate =>
          val tc2 = ctc.etc
          ntcs += tc2
          tcLuggage(tc2)=Map()
        case atc : AtomicTypeCoordinate =>
        case ditc : DomainInstanceTypeCoordinate =>
          assert (ditc.args.forall { tc => done contains tc })

          val domain = p.findDomain(ditc.dn)
          val types = getTypes(domain)
          types.foreach(
            t=>{
              val tc2 = makeTypeCoordinate(t.substitute(ditc.dt.typVarsMap))

              if (!(done contains tc2))
              {
                val tc2InflationMap =
                  (t match {
                    case dt2:DomainType =>
                      dt2.typVarsMap.map {
                        case (tv2 : TypeVar,t2 : Type) => tv2 -> (getFTVDepths(t2).map { case (ftv: TypeVar, d: Int) => d + tcLuggage(tc)(ftv) } ++ Seq(0)).max
                      }
                    case _ => Seq()
                  }
                    ).toMap

                if (tc2InflationMap.values.forall(v=>v<=tcThreshold))
                {
                  if (!tcLuggage.contains(tc2))
                    tcLuggage(tc2) = tc2InflationMap
                  else
                    tcLuggage(tc2) =
                      tcLuggage(tc2) ++ tc2InflationMap.map { case (tv,d) => tv -> (d + tcLuggage(tc2).getOrElse(tv,0)) }

                  assert (tcLuggage contains tc2)
                  ntcs += tc2

                }else{
//                  println("At domain \"" + tc + "\" skipped creating \"" + tc2 + "\"")
                }

              }
            }
          )
      }
      ntcs.foreach {
        tc2 =>{
          assert (tcLuggage contains tc2)
          done add tc2
          todo.enqueue(tc2)
        }
      }

    }

//    println("Calculating ground type instances done - total " + done.size)
    val result = done.map(_.t).toSet
//    println("Calculating ground type instances result done - total " + result.size)

    result
  }

  def getInstanceMembers(p:Program,dt : DomainType) : (Set[DomainFunc],Set[DomainAxiom]) = {
    val domain = p.findDomain(dt.domainName)

    (
      domain.functions.filter(f => collectTypes(substitute(f, dt.typVarsMap)).subsetOf(p.groundTypeInstances)).toSet,
      domain.axioms.filter(a => collectTypes(substitute(a, dt.typVarsMap)).subsetOf(p.groundTypeInstances)).toSet
      )

  }
  def showInstanceMembers(p:Program) = {
    for (ti <- p.groundTypeInstances)
    {
      ti match {
        case dt : DomainType =>
        {
          println("Members for Domain type " + dt.toString())
          val domain = p.findDomain(dt.domainName)
          val (fs,as) = getInstanceMembers(p,dt)
          for (f <- fs)
            println("   Function " + f.toString())
          for (a <- as)
            println("   Axiom " + a.toString())
          for (rf <- domain.functions.filter(f=> fs.forall((ff)=>ff.name!=f.name)))
            println("   Rejected Function " + rf.toString())
          for (ra <- domain.axioms.filter(a=> as.forall((aa)=>aa.name!=a.name)))
            println("   Rejected Axiom " + ra.toString())

/*
          val domain = p.findDomain(dt.domainName)
          for (f <- domain.functions){
            val rt = f.typ.substitute(dt.typVarsMap)
            val ats = f.formalArgs map (_.typ.substitute(dt.typVarsMap))
            val b = ((ats :+ rt).toSet.subsetOf(p.groundTypeInstances))
            println("   " + (if (b) "" else  "Rejected ") + "Function " + f.name + "(" + ats.mkString(",") + ") : " + rt.toString())
          }
          for (a <- domain.axioms){
            val types = p.deepCollect({case t : Type => t}).toSet
            val sts = (types map (_.substitute(dt.typVarsMap))).toSet
            val b = (sts.subsetOf(p.groundTypeInstances))
            println("   " + (if (b) "" else  "Rejected ") + "Axiom " + a.name + " : " + a.exp.toString() )
          }*/
        }
        case _ => {}

      }
    }

  }


  def getFTVDepths(t : Type) : Map[TypeVar,Int] = t match {
    case dt: DomainType =>
      dt.typVarsMap.flatMap {
        case (tv: TypeVar, t: Type) => getFTVDepths(t).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }
      }
    case ct: CollectionType => getFTVDepths(ct.elementType).map { case (tv2: TypeVar, d: Int) => tv2 -> d.+(1) }
    case tv: TypeVar => Map(tv -> 0)
    case at: BuiltInType => Map()
  }


  def down1Types(t:Type) : Set[Type] = t match {
    case dt: DomainType => dt.typVarsMap.values.toSet
    case ct: CollectionType => Set(ct.elementType)
    case bt: BuiltInType => Set()
    case tv: TypeVar => Set()
  }

  def downClosure(t:Type) : Set[Type] =
    Set(t) ++ down1Types(t).flatMap(downClosure)


  def getTypes(d:Domain) : Set[Type] = d.deepCollect{case t : Type => downClosure(t)}.flatten.toSet

  //////////////////////////////////////////////////////////////////////////////////////
  //Type Coordinates
  //A type coordinate is

  def makeTypeCoordinate(t:Type) : TypeCoordinate =
    t match {
      case ct  : CollectionType => CollectionTypeCoordinate(CollectionClass.getCC(ct),makeTypeCoordinate(ct.elementType))
      case bit : BuiltInType    => AtomicTypeCoordinate(bit)
      case dt  : DomainType     => new DomainInstanceTypeCoordinate(
        dt.domainName,
        dt.typeParameters.map(tv => makeTypeCoordinate(dt.typVarsMap(tv)))
      )(dt)
      case tv:TypeVar => throw new Exception("Internal error in type system - unexpected non-ground type <" + t.toString() + ">")
    }
  sealed abstract class TypeCoordinate(val t : Type){
    require(t.isConcrete)
    override def toString = t.toString()
    def down : Set[TypeCoordinate]
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

  case class AtomicTypeCoordinate(bit : BuiltInType) extends TypeCoordinate(bit){
    override def down : Set[TypeCoordinate] = Set(this)
  }
  case class CollectionTypeCoordinate(cc : CollectionClass.Value, etc : TypeCoordinate) extends TypeCoordinate(CollectionClass.makeCT(cc, etc.t)){
    override def down : Set[TypeCoordinate] = Set(this) ++ etc.down
  }
  case class DomainInstanceTypeCoordinate(dn : String,args:Seq[TypeCoordinate])(val dt:DomainType) extends TypeCoordinate(dt){
    override def down : Set[TypeCoordinate] = Set(this) ++ args.flatMap(_.down)
  }


  case class TarjanNode[N](n:N,var es:Array[TarjanNode[N]],var index:Int,var lowIndex:Int)
  class TarjanAR[N](val nodes:Map[N,TarjanNode[N]])
  {
    val r = new mutable.ListBuffer[mutable.Set[N]]()
    var index : Int = 0
    val stack = new mutable.Stack[N]()
    val set = new mutable.HashSet[N]()
  }
  def getSCCs[N, L](g: Map[N, Map[N, L]]): List[mutable.Set[N]] = {
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

  def getTVs(t:Type) : Set[TypeVar] =
    t match {
      case tv : TypeVar => Set(tv)
      case dt : DomainType =>
        (dt.typeParameters.toSet -- dt.typVarsMap.keys) ++ dt.typVarsMap.values.flatMap(getTVs)
      case ct : CollectionType => getTVs(ct.elementType)
      case _ => Set()
    }
  def getDomainTypeInstances(d:Domain) : Set[Type] =
    d.deepCollect {
      case t: Type => t
    }.toSet

  ///////////////////////////////////////////////////////////////////////////////////////////
  //End generic type instances
  ///////////////////////////////////////////////////////////////////////////////////////////
  ///////////////////////////////////////////////////////////////////////////////////////////

}
