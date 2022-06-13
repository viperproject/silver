package viper.silver.plugin.standard.inline

import viper.silver.ast._
import viper.silver.utility.NameGenerator

import scala.collection.mutable

class TriggerManager(program: Program, inlinePreds: Seq[Predicate], val names: NameGenerator) {
  val domainName: String = names.createUnique("PredTriggerDomain")
  val triggerMap: Map[String, DomainFunc] = {
    val preds = inlinePreds.iterator.map(p => (p.name, p)).toMap
    val res = mutable.Map[String, DomainFunc]()
    program.visit {
      case f: Forall =>
        f.autoTrigger.triggers.foreach(
          _.visit {
            case p: PredicateAccess =>
              val pred = preds(p.predicateName)
              res.put(pred.name, DomainFunc(names.createUnique(pred.name), pred.formalArgs, Bool)(pred.pos, pred.info, domainName, pred.errT))
          })
    }
    res.toMap
  }

  def wrap(p: PredicateAccessPredicate, body: Exp): Exp = {
    val pred = p.loc
    triggerMap.get(pred.predicateName) match {
      case None => body
      case Some(domFun) =>
        val dummy = LocalVarDecl(names.createUnique("dummy"), Bool)()
        val funcApp = DomainFuncApp(domFun, pred.args, Map())(p.pos, p.info, p.errT)
        Let(dummy, funcApp, body)(p.pos, p.info, p.errT)
    }
  }

  def mapTriggers(triggers: Seq[Trigger]): Seq[Trigger] = {
    triggers.map(_.transform {
      case p@PredicateAccess(args, name) =>
        DomainFuncApp(triggerMap(name), args, Map())(p.pos, p.info, p.errT)
    })
  }

  def intoDomain(): Option[Domain] = {
    val funcs = triggerMap.values.toSeq
    if (funcs.isEmpty) {
      None
    } else {
      Some(Domain(domainName, funcs, Seq())())
    }
  }
}
