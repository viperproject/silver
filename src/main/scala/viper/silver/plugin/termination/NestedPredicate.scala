package viper.silver.plugin.termination

import viper.silver.FastMessaging
import viper.silver.ast.utility.Consistency
import viper.silver.ast.utility.Statements.EmptyStmt
import viper.silver.ast._

import scala.collection.immutable.ListMap

/**
  * Adds nested statements for the used predicates to the check code.
  * Therefore it needs the following in the program:
  * "nested" domain function
  * "Loc" domain
  */
trait NestedPredicate extends TerminationCheck with RewriteFunctionBody[SimpleContext] {

  val nestedFunc: Option[DomainFunc] =  program.findDomainFunctionOptionally("nested")
  val locationDomain: Option[Domain] =  program.domains.find(_.name == "Loc") // findDomainOptionally()?

  // local variables for methods. Have to be added to the created method
  val neededLocalVars: collection.mutable.ListMap[Function, collection.mutable.ListMap[String, LocalVarDecl]] = collection.mutable.ListMap[Function, collection.mutable.ListMap[String, LocalVarDecl]]()

  private val neededLocFunctions: collection.mutable.ListMap[String, DomainFunc] = collection.mutable.ListMap[String, DomainFunc]()

  override def clear(): Unit = {
    neededLocFunctions.clear()
    neededLocalVars.clear()
  }

  /**
    * Creates a new program with the needed fields added to it
    *
    * @return a program
    */
  override def createCheckProgram(): Program = {

    if(neededLocFunctions.nonEmpty){
      assert(locationDomain.isDefined)
      val newLocDom = Domain(locationDomain.get.name,
        neededLocFunctions.values.toSeq,
        locationDomain.get.axioms,
        locationDomain.get.typVars)(locationDomain.get.pos, locationDomain.get.info, locationDomain.get.errT)

      domains(newLocDom.name) = newLocDom
    }

    super.createCheckProgram()
  }


  /**
    * Transforms an expression (e.g. function body) into a statement.
    * Parts of the expressions which stay expressions (e.g. the condition in a if clause)
    * are added in front as statements.
    * TODO: Expressions which cannot be transformed to statements (e.g. literals) are replaced
    * by the transfromExp.
    *
    * @return a statement representing the expression
    */
  override def transform: PartialFunction[(Exp, SimpleContext), Stmt] = {
    // TODO: unfolding should be here
    case (pap: PredicateAccessPredicate, c: SimpleContext) =>
      val func = c.func
      val permChecks = transform(pap.perm, c)
      val dec = decreasesMap.get(func)
      //Add the nested-assumption if the predicate has another predicate inside of its body
      dec match {
        case Some(DecreaseExp(_,_,_)) =>
          val pred: Predicate = program.findPredicate(pap.loc.predicateName)

          pred.body match {
            case Some(body) =>
              if (locationDomain.isDefined && nestedFunc.isDefined) {
                val formalArgs = pred.formalArgs map (_.localVar)
                //Generate nested-assumption
                val predBody = transformPredicateBody(body.replace(ListMap(formalArgs.zip(pap.loc.args):_*)), pap, c)
                Seqn(Seq(permChecks, predBody), Nil)(body.pos)
              } else {
                if (locationDomain.isEmpty) {
                  Consistency.messages ++= FastMessaging.message(
                    func, "missing location-domain")
                }
                if (nestedFunc.isEmpty) {
                  Consistency.messages ++= FastMessaging.message(
                    func, "missing nested-relation")
                }
                permChecks
              }
            //Predicate has no body
            case None => permChecks
          }
        //No decreasing clause
        case _ => permChecks
      }
    case d => super.transform(d)
  }

  /**
    * Traverses a predicate body and adds corresponding inhales of the 'nested'-Relation
    * iff a predicate is inside of this body
    *
    * @param body     the part of the predicate-body which should be analyzed
    * @param origPred the body of the original predicate which should be analyzed
    * @return statements with the generated inhales: (Inhale(nested(pred1, pred2)))
    */
  def transformPredicateBody(body: Exp, origPred: PredicateAccessPredicate, context: SimpleContext): Stmt = {
    // TODO: shouldn't the expression be checked for termination or at least replaced with dummy
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
          val varOfCallerPred: LocalVar = uniquePredLocVar(origPred.loc, context)
          val varOfCalleePred: LocalVar = uniquePredLocVar(calledPred.loc, context)

          //assign
          val assign1 = generateAssign(origPred, varOfCallerPred)
          val assign2 = generateAssign(calledPred, varOfCalleePred)

          //inhale nested-relation
          val params: Seq[TypeVar] = program.findDomain(nestedFunc.get.domainName).typVars
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
        val thn = transformPredicateBody(c.thn, origPred, context)
        val els = transformPredicateBody(c.els, origPred, context)
        If(c.cond, Seqn(Seq(thn), Nil)(c.pos), Seqn(Seq(els), Nil)(c.pos))(c.pos)
      case i: Implies =>
        val thn = transformPredicateBody(i.right, origPred, context)
        If(i.left, Seqn(Seq(thn), Nil)(i.pos), EmptyStmt)(i.pos)
      case b: BinExp =>
        val left = transformPredicateBody(b.left, origPred, context)
        val right = transformPredicateBody(b.right, origPred, context)
        Seqn(Seq(left, right), Nil)(b.pos)
      case u: UnExp => transformPredicateBody(u.exp, origPred, context)
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
  def generateAssign(pred: PredicateAccessPredicate, assLocation: LocalVar, argMap: ListMap[Exp, Exp] = ListMap.empty)
  : LocalVarAssign = {
    val domainOfPred: Domain = uniqueNameGen(pred.loc).asInstanceOf[Domain]
    val domainFunc = uniqueNameGen(pred).asInstanceOf[DomainFunc]
    val typVarMap: ListMap[TypeVar, Type] =
      ListMap(TypeVar(locationDomain.get.typVars.head.name) -> DomainType(domainOfPred, ListMap()))
    val assValue = DomainFuncApp(domainFunc, pred.loc.args.map(_.replace(argMap)), typVarMap)(pred.pos)
    LocalVarAssign(assLocation, assValue)(pred.pos)
  }

  /**
    * Generator of the predicate-variables, which represents the type 'predicate'.
    *
    * @param p      predicate which defines the type of the variable
    * @return a local variable with the correct type
    */
  def uniquePredLocVar(p: PredicateAccess, context: SimpleContext): LocalVar = {
    val func = context.func
    val predVarName = p.predicateName + "_" + p.args.hashCode().toString.replaceAll("-", "_")
    if (!neededLocalVars.contains(func)){
      neededLocalVars(func) = collection.mutable.ListMap()
    }
    if (neededLocalVars(func).contains(predVarName)) {
      //Variable already exists
      neededLocalVars(func)(predVarName).localVar
    } else {
      val info = SimpleInfo(Seq(p.predicateName + "_" + p.args.mkString(",")))
      val newLocalVar =
        LocalVar(predVarName)(DomainType(locationDomain.get,
          ListMap(TypeVar(locationDomain.get.typVars.head.name)
            -> DomainType(uniqueNameGen(p).asInstanceOf[Domain], ListMap()))),
          info = info)
      neededLocalVars(func)(predVarName) = LocalVarDecl(newLocalVar.name, newLocalVar.typ)(newLocalVar.pos, info)
      newLocalVar
    }
  }

  private def uniqueNameGen(node: Node): Node = {
    assert(node.isInstanceOf[PredicateAccess] ||
      node.isInstanceOf[PredicateAccessPredicate])
    node match {
      case p: PredicateAccess =>
        if (domains.values.exists(_.name == p.predicateName)) {
          domains.values.find(_.name == p.predicateName).get
        } else {
          if (domains.contains(p.predicateName)) {
            domains(p.predicateName)
          } else {
            val uniquePredName = uniqueName(p.predicateName + "_PredName")
            val newDomain = Domain(uniquePredName, Seq(), Seq(), Seq())(NoPosition)
            //domains(uniquePredName) = newDomain
            domains(p.predicateName) = newDomain
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
