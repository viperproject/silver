package viper.silver.testing

import org.scalatest.funsuite.AnyFunSuite
import org.scalatest.matchers.should.Matchers
import org.scalatest.{BeforeAndAfterAllConfigMap, ConfigMap}
import viper.silver.ast.{And, AnySetContains, Assert, BackendFuncApp, Domain, EqCmp, Exhale, Exp, Field, FieldAccess, FieldAccessPredicate, FieldAssign, Fold, Forall, FullPerm, Function, Implies, Inhale, IntLit, LocalVarAssign, LocalVarDecl, Method, NeCmp, Not, Predicate, PredicateAccess, PredicateAccessPredicate, Program, Ref, Result, Seqn, SetType, Stmt}
import viper.silver.ast.utility.{BVFactory, FloatFactory, RoundingMode}
import viper.silver.verifier.{Failure, Success, Verifier}
import viper.silver.verifier.errors.{AssertFailed, PostconditionViolated}

trait BackendTypeTest extends AnyFunSuite with Matchers with BeforeAndAfterAllConfigMap {

  def generateTypeCombinationTest(success: Boolean) : (Program, Assert) = {
    val t = if (success) BVFactory(23).typ else FloatFactory(23, 11, RoundingMode.RNE).typ
    val p1_decl = LocalVarDecl("three", t)()
    val p1_ref = p1_decl.localVar
    val p2_decl = LocalVarDecl("lol", SetType(t))()
    val p2_ref= p2_decl.localVar
    val element_in_param = AnySetContains(p1_ref, p2_ref)()

    val assume = Inhale(element_in_param)()
    val assert = Assert(element_in_param)()
    val body = if (success) Seq(assume, assert) else Seq(assert)
    val domain = if (success) BVFactory(23).constructDomain(Seq()) else FloatFactory(23, 11, RoundingMode.RNE).constructDomain(Seq())
    (wrapInProgram(Seq(domain), body, Seq(p1_decl, p2_decl), Seq()), assert)
  }

  def generateFieldTypeTest(success: Boolean) : (Program, Assert) = {
    val t = if (!success) BVFactory(23).typ else FloatFactory(23, 11, RoundingMode.RNE).typ
    val field = Field("f", t)()
    val p1_decl = LocalVarDecl("three", Ref)()
    val p1_ref = p1_decl.localVar
    val p2_decl = LocalVarDecl("lol", SetType(t))()
    val p2_ref= p2_decl.localVar
    val fieldAcc = FieldAccess(p1_ref, field)()
    val perm = FieldAccessPredicate(fieldAcc, Some(FullPerm()()))()
    val element_in_param = AnySetContains(fieldAcc, p2_ref)()

    val getPerm = Inhale(perm)()
    val assume = Inhale(element_in_param)()
    val assert = Assert(element_in_param)()
    val body = if (success) Seq(getPerm, assume, assert) else Seq(getPerm, assert)
    val domain = if (!success) BVFactory(23).constructDomain(Seq()) else FloatFactory(23, 11, RoundingMode.RNE).constructDomain(Seq())
    (wrapInProgram(Seq(domain), body, Seq(p1_decl, p2_decl), Seq(), fields = Seq(field)), assert)
  }

  def generateFloatQPTest() : Program = {
    val rne = RoundingMode.RNE
    val fp = FloatFactory(24, 8, rne)
    val fld = Field("myfield", fp.typ)()
    val setParam = LocalVarDecl("refs", SetType(Ref))()
    val floatParam = LocalVarDecl("val", fp.typ)()
    val x = LocalVarDecl("x", Ref)()
    val qpBody = Implies(AnySetContains(x.localVar, setParam.localVar)(), FieldAccessPredicate(FieldAccess(x.localVar, fld)(), None)())()
    val qp = Forall(Seq(x), Seq(), qpBody)()
    val inhaleQp = Inhale(qp)()
    val fieldInfoBody = Implies(AnySetContains(x.localVar, setParam.localVar)(), NeCmp(FieldAccess(x.localVar, fld)(), floatParam.localVar)())()
    val fieldInfoQuant = Forall(Seq(x), Seq(), fieldInfoBody)()
    val inhaleFieldInfo = Inhale(fieldInfoQuant)()
    wrapInProgram(Seq(fp.constructDomain(Seq())), Seq(inhaleQp, inhaleFieldInfo), Seq(setParam, floatParam), Seq(), Seq(fld))
  }

  def generateFloatOpTest(success: Boolean) : (Program, Assert) = {
    val rne = RoundingMode.RNE
    val fp = FloatFactory(24, 8, rne)
    val first = 1081081856 // 3.75
    val second = 1103888384 // 25.5
    val result = 1105854464 // 29.25
    val bv32 = BVFactory(32)
    val from_int = bv32.from_int("toBV32")
    val to_fp = fp.from_bv("tofp")
    val fp_eq = fp.eq("fp_eq")
    val fp_add = fp.add("fp_add")

    val first_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(first)()))()))()
    val second_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(second)()))()))()
    val result_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(result)()))()))()

    val zero_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(0)()))()))()

    val addition = BackendFuncApp(fp_add, Seq(first_float, second_float))()
    val result_addition = BackendFuncApp(fp_add, Seq(result_float, if (success) zero_float else first_float))()

    val equality = BackendFuncApp(fp_eq, Seq(addition, result_addition))()
    val assert = Assert(equality)()
    (wrapInProgram(Seq(bv32.constructDomain(Seq(from_int)), fp.constructDomain(Seq(to_fp, fp_eq, fp_add))), Seq(assert), Seq(), Seq()), assert)
  }

  def generateFloatMinMaxTest(success: Boolean) : (Program, Assert) = {
    val rne = RoundingMode.RNE
    val fp = FloatFactory(24, 8, rne)
    val first = 1081081856 // 3.75
    val second = 1103888384 // 25.5
    val bv32 = BVFactory(32)
    val from_int = bv32.from_int("toBV32")
    val to_fp = fp.from_bv("tofp")
    val fp_eq = fp.eq("fp_eq")
    val fp_min = fp.min("fp_min")
    val fp_max = fp.max("fp_max")

    val first_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(first)()))()))()
    val second_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(second)()))()))()

    val min = BackendFuncApp(fp_min, Seq(first_float, second_float))()
    val max = BackendFuncApp(fp_max, Seq(first_float, second_float))()

    val equality_min = BackendFuncApp(fp_eq, Seq(min, first_float))()
    val equality_max = BackendFuncApp(fp_eq, Seq(max, second_float))()
    val equality = And(equality_min, equality_max)()
    val assert = Assert(if (success) equality else Not(equality)())()

    (wrapInProgram(Seq(bv32.constructDomain(Seq(from_int)), fp.constructDomain(Seq(to_fp, fp_eq, fp_min, fp_max))), Seq(assert), Seq(), Seq()), assert)
  }

  def generateFloatOpFunctionTest(success: Boolean) : (Program, Function, Exp) = {
    val rne = RoundingMode.RNE
    val fp = FloatFactory(24, 8, rne)
    val first = 1081081856 // 3.75
    val second = 1103888384 // 25.5
    val result = 1105854464 // 29.25
    val bv32 = BVFactory(32)
    val from_int = bv32.from_int("toBV32")
    val to_fp = fp.from_bv("tofp")
    val fp_eq = fp.eq("fp_eq")
    val fp_add = fp.add("fp_add")

    val first_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(first)()))()))()
    val second_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(second)()))()))()
    val result_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(result)()))()))()

    val zero_float = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(0)()))()))()

    val addition = BackendFuncApp(fp_add, Seq(first_float, second_float))()
    val result_addition = BackendFuncApp(fp_add, Seq(result_float, if (success) zero_float else first_float))()

    val equality = BackendFuncApp(fp_eq, Seq(Result(fp.typ)(), result_addition))()

    val fun = Function("test", Seq(), fp.typ, Seq(), Seq(equality), Some(addition))()
    val program = Program(Seq(fp.constructDomain(Seq(to_fp, fp_eq, fp_add)), bv32.constructDomain(Seq(from_int))), Seq(), Seq(fun), Seq(), Seq(), Seq())()
    (program, fun, equality)
  }


  def generatePredicateTest() : Program = {
    val rne = RoundingMode.RNE
    val fp = FloatFactory(52, 12, rne)
    val value = BigInt("4591870180066957722")
    val bv64 = BVFactory(64)
    val from_int = bv64.from_int("toBV64")
    val to_fp = fp.from_bv("tofp")
    val field = Field("val_float", fp.typ)()
    val selfVar = LocalVarDecl("self", Ref)()
    val fieldAcc = FieldAccess(selfVar.localVar, field)()
    val fieldAccPred = FieldAccessPredicate(fieldAcc, Some(FullPerm()()))()
    val pred = Predicate("f64", Seq(selfVar), Some(fieldAccPred))()

    val inhale = Inhale(fieldAccPred)()
    val fpVal = BackendFuncApp(to_fp, Seq(BackendFuncApp(from_int, Seq(IntLit(value)()))()))()
    val assign = FieldAssign(fieldAcc, fpVal)()
    val predAcc = PredicateAccess(Seq(selfVar.localVar), pred.name)()
    val predAccPred = PredicateAccessPredicate(predAcc, None)()
    val fold = Fold(predAccPred)()
    val exhale = Exhale(predAccPred)()

    val body = Seqn(Seq(inhale, assign, fold, exhale), Seq())()
    val method = Method("m_id", Seq(), Seq(selfVar), Seq(), Seq(), Some(body))()
    val domains = Seq(fp.constructDomain(Seq(to_fp)), bv64.constructDomain(Seq(from_int)))
    val prog = Program(domains, Seq(field), Seq(), Seq(pred), Seq(method), Seq())()

    prog
  }

  def generateBvOpTest(success: Boolean) : (Program, Assert) = {
    val bv23 = BVFactory(23)
    val from_int = bv23.from_int("toBV23")
    val two_lit = IntLit(2)()
    val three_lit = IntLit(3)()
    val one_lit = IntLit(1) ()
    val two = BackendFuncApp(from_int, Seq(two_lit))()
    val three = BackendFuncApp(from_int, Seq(three_lit))()
    val one = BackendFuncApp(from_int, Seq(one_lit))()
    val result_decl = LocalVarDecl("three", bv23.typ)()
    val result_ref = result_decl.localVar
    val assign = LocalVarAssign(result_ref, if (success) three else one)()
    val xor = bv23.xor("xorBV23")
    val xor_app = BackendFuncApp(xor, Seq(one, two))()
    val equality1 = EqCmp(result_ref, xor_app)()
    val assertion1 = Assert(equality1)()
    val domain = bv23.constructDomain(Seq(from_int, xor))
    (wrapInProgram(Seq(domain), Seq(assign, assertion1), Seq(), Seq(result_decl)), assertion1)
  }

  def generateBvOpTest2() : Program = {
    val bv23 = BVFactory(23)
    val from_int = bv23.from_int("toBV23")
    val two_lit = IntLit(2)()
    val one_lit = IntLit(1) ()
    val two = BackendFuncApp(from_int, Seq(two_lit))()
    val one = BackendFuncApp(from_int, Seq(one_lit))()
    val res_decl = LocalVarDecl("res", bv23.typ)()
    val res = res_decl.localVar
    val xor = bv23.xor("xorBV23")
    val xnor = bv23.xnor("xnorBV23")
    val and = bv23.and("andBV23")
    val nand = bv23.nand("nandBV23")
    val or = bv23.or("orBV23")
    val nor = bv23.nor("norBV23")
    val add = bv23.add("addBV23")
    val sub = bv23.sub("subBV23")
    val mul = bv23.mul("mulBV23")
    val smod = bv23.smod("smodBV23")
    val srem = bv23.srem("sremBV23")
    val udiv = bv23.udiv("udivBV23")
    val urem = bv23.urem("uremBV23")
    val shl = bv23.shl("shlBV23")
    val lshr = bv23.lshr("lshrBV23")
    val ashr = bv23.ashr("ashrBV23")
    val domain = bv23.constructDomain(Seq(from_int, xor, xnor, and, nand, or, nor, add, sub, mul, smod, srem, udiv, urem, shl, lshr, ashr))
    wrapInProgram(
      Seq(domain),
      Seq(
        LocalVarAssign(res, BackendFuncApp(xor, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(xnor, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(and, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(nand, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(or, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(nor, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(add, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(sub, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(mul, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(smod, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(srem, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(udiv, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(urem, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(shl, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(lshr, Seq(one, two))())(),
        LocalVarAssign(res, BackendFuncApp(ashr, Seq(one, two))())(),
      ), Seq(), Seq(res_decl))
  }

  def wrapInProgram(domains: Seq[Domain], stmts: Seq[Stmt], params: Seq[LocalVarDecl], vars: Seq[LocalVarDecl], fields: Seq[Field] = Seq()): Program = {
    val block = Seqn(stmts, vars)()
    val method = Method("test", params, Seq(), Seq(), Seq(), Some(block))()
    Program(domains, fields, Seq(), Seq(), Seq(method), Seq())()
  }

  val verifier : Verifier

  override def beforeAll(configMap: ConfigMap): Unit = {
    verifier.parseCommandLine(Seq("dummy.vpr"))
    verifier.start()
  }

  override def afterAll(configMap: ConfigMap): Unit = {
    verifier.stop()
  }

  test("typeCombinationSuccess") {
    val (prog, _) = generateTypeCombinationTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("typeCombinationFail") {
    val (prog, assertNode) = generateTypeCombinationTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(a, _, _))) if a == assertNode => true
      case _ => false
    })
  }

  test("fieldTypeSuccess") {
    val (prog, _) = generateFieldTypeTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("fieldQpTest") {
    val prog = generateFloatQPTest()
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("fieldTypeFail") {
    val (prog, assertNode) = generateFieldTypeTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(a, _, _))) if a == assertNode => true
      case _ => false
    })
  }

  test("bvOpSuccess") {
    val (prog, _) = generateBvOpTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("bvOpFail") {
    val (prog, assertNode) = generateBvOpTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(a, _, _))) if a == assertNode => true
      case _ => false
    })
  }

  test("bvOp2Success") {
    val prog = generateBvOpTest2()
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("floatOpSuccess") {
    val (prog, _) = generateFloatOpTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("floatOpFail") {
    val (prog, assertNode) = generateFloatOpTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(a, _, _))) if a == assertNode => true
      case _ => false
    })
  }

  test("floatMinMaxSuccess") {
    val (prog, _) = generateFloatMinMaxTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("floatMinMaxFail") {
    val (prog, assertNode) = generateFloatMinMaxTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(a, _, _))) if a == assertNode => true
      case _ => false
    })
  }

  test("floatOpFunctionSuccess") {
    val (prog, _, _) = generateFloatOpFunctionTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("floatOpFunctionFail") {
    val (prog, fun, exp) = generateFloatOpFunctionTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(PostconditionViolated(e, f, _, _))) if e == exp && fun == f => true
      case _ => false
    })
  }

  test("predicateSuccess") {
    val prog = generatePredicateTest()
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

}
