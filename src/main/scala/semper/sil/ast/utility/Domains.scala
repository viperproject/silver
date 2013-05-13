package semper.sil.ast.utility

import scala.collection.immutable.ListSet
import semper.sil.ast._

/** Utility methods for domain-related AST nodes. */
object Domains {
  def collectTypeVars(ts: Seq[Type]): Seq[TypeVar] = ts collect {case t: TypeVar => t}

  def collectTypeVars(t: Type): Seq[TypeVar] = t match {
    case tv: TypeVar => Seq(tv)
    case _ => Nil
  }

  def freeTypeVars(df: DomainFunc): Seq[TypeVar] =
    collectTypeVars(df.formalArgs map (_.typ)) ++ collectTypeVars(df.typ)

  def freeTypeVars(da: DomainAxiom): Seq[TypeVar] = {
    var ts = ListSet.empty[TypeVar]
    da.exp visit {case t: Typed => ts ++= collectTypeVars(t.typ)}
    ts.toSeq
  }

  def freeTypeVars(dm: DomainMember) = dm match {
    case df: DomainFunc => freeTypeVars(df)
    case da: DomainAxiom => freeTypeVars(da)
  }

  def domainMembers(d: Domain): Map[DomainMember, Domain] =
    (d.functions.map((_, d)) ++ d.axioms.map((_, d))).toMap

  def domainMembers(p: Program): Map[DomainMember, Domain] =
    p.domains.flatMap(domainMembers).toMap

  /**
   * Returns the set of concrete domain types that are used in the AST rooted at `n`.
   * @param n The root of a tree.
   * @return The set of concrete domain types that are used in the given AST. For each `dt` in the returned set,
   *         `dt.isisConcrete` holds.
   */
  def concreteDomainTypes(n: Node): Seq[DomainType] = {
    var instances: ListSet[DomainType] = ListSet.empty

    n visit {
      case d: Domain if d.typVars.isEmpty => instances += DomainType(d, Map.empty)
      case t: Typed => t.typ match {
        //        case dfa: DomainFuncApp =>
        //          val dt = DomainType(dfa.func.do, dfa.typVarMap)
        case dt: DomainType if dt.isConcrete => instances += dt
        case _ => /* Ignore other types */
      }
    }

    println("instances = " + instances.mkString(", "))

    var newInstances = instances

    while (newInstances.nonEmpty) {
      val prevNewInstances = newInstances
      newInstances = ListSet.empty

      prevNewInstances foreach (ndt => ndt.domain visit {
        case t: Typed => t.typ match {
          case dt: DomainType =>
            val substitutedDt = dt.substitute(ndt.typVarsMap)
            if (substitutedDt.isConcrete) newInstances += substitutedDt
          case _ => /* Ignore other types */
        }
      })

      newInstances = newInstances diff instances
      instances = instances union newInstances
    }

    instances.toSeq
  }
}
