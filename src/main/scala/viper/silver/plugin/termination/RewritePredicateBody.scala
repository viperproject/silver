package viper.silver.plugin.termination

import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast.{AccessPredicate, BinExp, CondExp, Domain, DomainFunc, DomainFuncApp, DomainType, Exp, FieldAccessPredicate, If, Implies, Inhale, Int, LocalVar, LocalVarAssign, LocalVarDecl, MagicWand, NoPosition, Node, PredicateAccess, PredicateAccessPredicate, Seqn, SimpleInfo, Stmt, Type, TypeVar, UnExp}

import scala.collection.immutable.ListMap
import scala.collection.mutable

trait RewritePredicateBody extends TerminationCheck {

  val neededLocFunctions: mutable.ListMap[String, DomainFunc] = collection.mutable.ListMap[String, DomainFunc]()

  override def clear(): Unit = {
    neededLocFunctions.clear()
    super.clear()
  }

  /**
    * Traverses a predicate body and adds corresponding inhales of the 'nested'-Relation
    * iff a predicate is inside of this body
    *
    * @param body     the part of the predicate-body which should be analyzed
    * @param origPred the body of the original predicate which should be analyzed
    * @return statements with the generated inhales: (Inhale(nested(pred1, pred2)))
    */
  def rewritePredBodyAsExp(body: Exp, origPred: PredicateAccessPredicate): Stmt = {

    body match {
      case ap: AccessPredicate => ap match {
        case FieldAccessPredicate(_, _) => EmptyStmt
        case calledPred: PredicateAccessPredicate =>
          assert(locationDomain.isDefined)
          assert(nestedFunc.isDefined)

          //predicate-Domains (p_PredName)
          val domainOfCallerPred: Domain = uniqueNameGen(origPred.loc).asInstanceOf[Domain]
          val domainOfCalleePred: Domain = uniqueNameGen(calledPred.loc).asInstanceOf[Domain]

          //local variables
          val varOfCallerPred: LocalVar = uniquePredLocVar(origPred.loc)
          val varOfCalleePred: LocalVar = uniquePredLocVar(calledPred.loc)

          //assign
          val assign1 = generateAssign(origPred, varOfCallerPred)
          val assign2 = generateAssign(calledPred, varOfCalleePred)

          //inhale nested-relation
          val params: Seq[TypeVar] = usedNames(nestedFunc.get.domainName).asInstanceOf[Domain].typVars
          val types: Seq[Type] =
            Seq(DomainType(domainOfCalleePred, ListMap()), DomainType(domainOfCallerPred, ListMap()), Int)

          val mapNested: ListMap[TypeVar, Type] = ListMap(params.zip(types):_*)
          val assume = Inhale(DomainFuncApp(nestedFunc.get,
            Seq(varOfCalleePred, varOfCallerPred),
            mapNested)(calledPred.pos))(calledPred.pos)

          Seqn(Seq(assign1, assign2, assume), Nil)(calledPred.pos)
        case mw: MagicWand =>
          sys.error(s"Unexpectedly found resource access node $mw")
      }
      case c: CondExp =>
        val thn = rewritePredBodyAsExp(c.thn, origPred)
        val els = rewritePredBodyAsExp(c.els, origPred)
        If(c.cond, Seqn(Seq(thn), Nil)(c.pos), Seqn(Seq(els), Nil)(c.pos))(c.pos)
      case i: Implies =>
        val thn = rewritePredBodyAsExp(i.right, origPred)
        If(i.left, Seqn(Seq(thn), Nil)(i.pos), EmptyStmt)(i.pos)
      case b: BinExp =>
        val left = rewritePredBodyAsExp(b.left, origPred)
        val right = rewritePredBodyAsExp(b.right, origPred)
        Seqn(Seq(left, right), Nil)(b.pos)
      case u: UnExp => rewritePredBodyAsExp(u.exp, origPred)
      case _ => EmptyStmt
    }
  }

  /**
    * Generates for a predicate and a variable the corresponding assignment
    * it generates the viper-representation of a predicate (via loc-domain and the proper domain-function)
    * and assign it to the given value
    *
    * @param pred        the predicate which defines the predicate-Domain and predicate-domainFunc
    * @param assLocation the variable, which should be assigned
    * @param argMap      an optional mapping used for replacing the arguments of the predicate
    * @return an assignment of the given variable to the representation of a predicate with the corresponding arguments
    */
  private def generateAssign(pred: PredicateAccessPredicate, assLocation: LocalVar, argMap: ListMap[Exp, Exp] = ListMap.empty)
  : LocalVarAssign = {
    val domainOfPred: Domain = uniqueNameGen(pred.loc).asInstanceOf[Domain]
    val domainFunc = uniqueNameGen(pred).asInstanceOf[DomainFunc]
    val typVarMap: ListMap[TypeVar, Type] =
      ListMap(TypeVar(locationDomain.get.typVars.head.name) -> DomainType(domainOfPred, ListMap()))
    val assValue = DomainFuncApp(domainFunc, pred.loc.args.map(_.replace(argMap)), typVarMap)(pred.pos)
    LocalVarAssign(assLocation, assValue)(pred.pos)
  }


  /**
    * Generator of the predicate-variables, which represents the type 'predicate'
    *
    * @param p      predicate which defines the type of the variable
    * @param argMap optional replacement for the arguments
    * @return a local variable with the correct type
    */
  private def uniquePredLocVar(p: PredicateAccess, argMap: ListMap[Exp, Exp] = ListMap.empty): LocalVar = {
    val args = p.args map (_.replace(argMap))
    val predVarName = p.predicateName + "_" + args.hashCode().toString.replaceAll("-", "_")
    if (neededLocalVars.contains(p.predicateName)) {
      //Variable already exists
      neededLocalVars(p.predicateName).localVar
    } else {
      val info = SimpleInfo(Seq(p.predicateName + "_" + args.mkString(",")))
      val newLocalVar =
        LocalVar(predVarName)(DomainType(locationDomain.get,
          ListMap(TypeVar(locationDomain.get.typVars.head.name)
            -> DomainType(uniqueNameGen(p).asInstanceOf[Domain], ListMap()))),
          info = info)
      neededLocalVars(predVarName) = LocalVarDecl(newLocalVar.name, newLocalVar.typ)(newLocalVar.pos, info)
      newLocalVar
    }
  }

  private def uniqueNameGen(node: Node): Node = {
    assert(node.isInstanceOf[PredicateAccess] ||
      node.isInstanceOf[PredicateAccessPredicate])
    node match {
      case p: PredicateAccess =>
        if (neededDomains.values.exists(_.name == p.predicateName)) {
          neededDomains.values.find(_.name == p.predicateName).get
        } else {
          if (neededDomains.contains(p.predicateName)) {
            neededDomains(p.predicateName)
          } else {
            val uniquePredName = uniqueName(p.predicateName + "_PredName")
            val newDomain = Domain(uniquePredName, Seq(), Seq(), Seq())(NoPosition)
            //domains(uniquePredName) = newDomain
            neededDomains(p.predicateName) = newDomain
            newDomain
          }
        }
      case pa: PredicateAccessPredicate =>
        if (neededLocFunctions.contains(pa.loc.predicateName)) {
          neededLocFunctions(pa.loc.predicateName)
        } else {
          val uniquePredFuncName =
            uniqueName("loc_" + pa.loc.args.map(_.typ).mkString("_").replaceAll("\\[", "").replaceAll("\\]", ""))
          val pred = program.findPredicate(pa.loc.predicateName)
          val newLocFunc =
            DomainFunc(uniquePredFuncName,
              pred.formalArgs,
              DomainType(locationDomain.get,
                ListMap(locationDomain.get.typVars.head -> locationDomain.get.typVars.head))
            )(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.name, locationDomain.get.errT)

          //domainfunctions(uniquePredFuncName) = newLocFunc
          neededLocFunctions(pa.loc.predicateName) = newLocFunc
          newLocFunc
        }
    }
  }


}
