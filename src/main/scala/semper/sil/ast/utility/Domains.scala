package semper.sil.ast.utility

import scala.language.postfixOps
import collection.mutable.{HashMap => MHashMap, MultiMap => MMultiMap, Set => MSet}
import semper.sil.ast._

/** Utility methods for domain-related AST nodes. */
object Domains {
  def collectTypeVars(types: Set[Type]): Set[TypeVar] = types flatMap {
    case t: TypeVar => Set(t)
    case DomainType(domain, typeVarsMap) => (domain.typVars filterNot typeVarsMap.contains).toSet
    case _ => Set[TypeVar]()
  }

  def collectTypeVars(typ: Type): Set[TypeVar] = collectTypeVars(Set(typ))

  def freeTypeVars(domainFunction: DomainFunc): Set[TypeVar] = (
       collectTypeVars(domainFunction.formalArgs map (_.typ) toSet)
    ++ collectTypeVars(domainFunction.typ))

  def freeTypeVars(domainAxiom: DomainAxiom): Set[TypeVar] = {
    var ts = Set[TypeVar]()
    domainAxiom.exp visit {case t: Typed => ts ++= collectTypeVars(t.typ)}
    ts
  }

  def freeTypeVars(domainMember: DomainMember): Set[TypeVar] = domainMember match {
    case df: DomainFunc => freeTypeVars(df)
    case da: DomainAxiom => freeTypeVars(da)
  }

  def freeTypeVars(domain: Domain): Set[TypeVar] = domain.typVars.toSet

  def domainMembers(domain: Domain): Map[DomainMember, Domain] =
    (domain.functions.map((_, domain)) ++ domain.axioms.map((_, domain))).toMap

  def domainMembers(program: Program): Map[DomainMember, Domain] =
    program.domains.flatMap(domainMembers).toMap

  /**
   * Returns the set of concrete domain types that are used in the given program.
   * @param program A program
   * @return The set of concrete domain types that are used in the given program. For all `dt` in
   *         the returned set, `dt.isConcrete` holds.
   */
  def collectConcreteDomainTypes(program: Program): Set[DomainType] = {
    var domains: Set[DomainType] = Set()
    var newDomains: Set[DomainType] = Set()

    var ds: Iterable[DomainType] = program.domains filter (_.typVars.isEmpty) map (DomainType(_, Map.empty))
//    println("Domain types w/o type variables")
//    ds foreach (dt => println("  " + toStringDT(dt)))
    domains ++= ds

    ds = collectConcreteDomainTypes(program, Map())
//    println("Domain types w/o additional substitution")
//    ds foreach (dt => println("  " + toStringDT(dt)))
    domains ++= ds

    newDomains = domains
    var continue = newDomains.nonEmpty

    while (continue) {
      newDomains = newDomains flatMap (dt => collectConcreteDomainTypes(dt.domain, dt.typVarsMap))

      newDomains = newDomains -- domains
      continue = newDomains.nonEmpty
//      println("Domain types fix-point iteration")
//      newDomains foreach (dt => println(toStringDT(dt)))

      domains ++= newDomains
    }

    domains
  }

  private def collectConcreteDomainTypes(node: Node, typeVarsMap: Map[TypeVar, Type])
                                        : Set[DomainType] = {

    var domains: Set[DomainType] = Set()

    node visit {
      case t: Typed => t.typ match {
        case dt: DomainType =>
          val substitutedDt = dt.substitute(typeVarsMap)
          if (substitutedDt.isConcrete) domains += substitutedDt

        case _ => /* Ignore other types */
      }
    }

    domains
  }

  sealed trait DomainMemberInstance {
    def member: DomainMember
    def typeVarsMap: Map[TypeVar, Type]

    lazy val typeVars = freeTypeVars(member)
    lazy val isConcrete = typeVars forall typeVarsMap.contains

    override lazy val toString = s"$member where $typeVarsMap"
  }

  case class DomainFunctionInstance(member: DomainFunc, typeVarsMap: Map[TypeVar, Type]) extends DomainMemberInstance
  case class DomainAxiomInstance(member: DomainAxiom, typeVarsMap: Map[TypeVar, Type]) extends DomainMemberInstance

  private type InstanceCollection =
    MHashMap[Domain, MSet[DomainMemberInstance]] with MMultiMap[Domain, DomainMemberInstance]

  private object InstanceCollection {
    def empty: InstanceCollection =
      new MHashMap[Domain, MSet[DomainMemberInstance]] with MMultiMap[Domain, DomainMemberInstance]
  }

  def collectConcreteDomainMemberInstances(program: Program, concreteDomainTypes: Set[DomainType])
                                          : Map[Domain, Set[DomainMemberInstance]] = {

    val membersWithSource = domainMembers(program)

    val instances = InstanceCollection.empty
    var newInstances = InstanceCollection.empty

    /* Get member instances from concrete domain types. */
    insert(
      instances,
      concreteDomainTypes map {case dt =>
        val members: MSet[DomainMemberInstance] =
          MSet((dt.domain.functions.map(DomainFunctionInstance(_, dt.typVarsMap))
                ++ dt.domain.axioms.map(DomainAxiomInstance(_, dt.typVarsMap))
               ):_*)

        (dt.domain, members)})

    /* Get member instances from the program. Since the passed type variable mapping is empty,
     * this will only collect domain functions from domain function applications in which all
     * type variables are instantiated with concrete types. This is always the case for domain
     * function applications that occur in program expressions and program assertions because
     * there cannot be any type variables in those contexts, but it is not necessarily the case
     * for domain function applications that occur inside domain declarations.
     */
    insert(newInstances,
           collectConcreteDomainMemberInstances(program, Map[TypeVar, Type](), membersWithSource))

//    println("\n[collectConcreteDomainMemberInstances]")
//    println("from concrete domain types")
//    printIC(instances)
//    println("from the program without any type var subst")
//    printIC(diff(newInstances, instances))

    insert(instances, newInstances)

    var continue = newInstances.nonEmpty

    while (continue) {
      val nextNewInstances = InstanceCollection.empty

      newInstances foreach {case (domain, memberInstances) =>
        memberInstances foreach {instance =>
          val ms =
            collectConcreteDomainMemberInstances(membersWithSource(instance.member),
                                                 instance.typeVarsMap,
                                                 membersWithSource)

          insert(nextNewInstances, ms)
      }}

      continue = false
      nextNewInstances foreach {case (domain, memberInstances) =>
        memberInstances foreach {instance =>
          if (!instances.entryExists(domain, _ == instance)) continue = true}}

//      println("from a fix-point iteration")
//      println("  continue? " + continue)
//      printIC(diff(nextNewInstances, instances))

      newInstances = nextNewInstances
      insert(instances, newInstances)
    }

    (instances mapValues { _.toSet }).toMap[Domain, Set[DomainMemberInstance]]
  }

  private def collectConcreteDomainMemberInstances(node: Node,
                                                   typeVarsMap: Map[TypeVar, Type],
                                                   membersWithSource: Map[DomainMember, Domain])
                                                  : InstanceCollection = {

    assert(typeVarsMap.values forall (_.isConcrete), "Expected type variable mapping to only map to concrete types")

    val instances = InstanceCollection.empty

    node visit {
      case dfa: DomainFuncApp =>
        val combinedTypeVarsMap = typeVarsMap ++ dfa.typVarMap

        if (freeTypeVars(dfa.func) forall (v => combinedTypeVarsMap.contains(v) && combinedTypeVarsMap(v).isConcrete)) {
//          println("[dfa] " + DomainFunctionInstance(dfa.func, combinedTypeVarsMap))
          instances.addBinding(membersWithSource(dfa.func), DomainFunctionInstance(dfa.func, combinedTypeVarsMap))
        }

      case df: DomainFunc if freeTypeVars(df) forall typeVarsMap.contains =>
//        println("[df] " + DomainFunctionInstance(df, typeVarsMap))
//        println("  freeTypeVars(df) = " + freeTypeVars(df))
//        println("  typeVarsMap = " + typeVarsMap)
        instances.addBinding(membersWithSource(df), DomainFunctionInstance(df, typeVarsMap))

      case da: DomainAxiom if freeTypeVars(da) forall typeVarsMap.contains =>
//        println("da = " + da)
//        println("domain = " + toStringD(membersWithSource(da)))
//        println("freeTypeVars(da) = " + freeTypeVars(da))
//        println("typeVarsMap = " + typeVarsMap)
        instances.addBinding(membersWithSource(da), DomainAxiomInstance(da, typeVarsMap))
    }

    instances
  }

  private def insert(into: InstanceCollection, from: Iterable[(Domain, Iterable[DomainMemberInstance])]) {
    from foreach {case (domain, memberInstances) =>
      memberInstances foreach (into.addBinding(domain, _))
    }
  }

  def toStringD(d: Domain) = d.name + d.typVars.mkString("[",",","]")

  def toStringDT(dt: DomainType) =
    dt.domain.name + dt.domain.typVars.mkString("[",",","]") + " where " + dt.typVarsMap

  def printIC(ic: Iterable[(Domain, Iterable[DomainMemberInstance])]) {
    ic foreach {case (domain, memberInstances) =>
//      println("  domain = " + toStringD(domain))
      memberInstances foreach (mi => println("    " + mi))
    }
  }

  def diff(ic1: InstanceCollection, ic2: InstanceCollection): InstanceCollection = {
    val ic3 = InstanceCollection.empty

    ic1 foreach {case (domain, memberInstances) =>
      memberInstances foreach {instance =>
        if (!ic2.entryExists(domain, _ == instance)) ic3.addBinding(domain, instance)}}

    ic3
  }
}
