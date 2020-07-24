package viper.silver.testing

import org.scalatest.{BeforeAndAfterAllConfigMap, ConfigMap, FunSuite, Matchers}
import viper.silver.ast.{AnySetContains, Assert, EqCmp, Field, FieldAccess, FieldAccessPredicate, FullPerm, Inhale, IntLit, LocalVarAssign, LocalVarDecl, Method, Program, Ref, SMTFuncApp, Seqn, SetType, Stmt}
import viper.silver.ast.utility.{BVFactory, FloatFactory, RoundingMode}
import viper.silver.verifier.{Failure, Success, Verifier}
import viper.silver.verifier.errors.AssertFailed

trait SMTTypeTest extends FunSuite with Matchers with BeforeAndAfterAllConfigMap {

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
    (wrapInProgram(body, Seq(p1_decl, p2_decl), Seq()), assert)
  }

  def generateFieldTypeTest(success: Boolean) : (Program, Assert) = {
    val t = if (!success) BVFactory(23).typ else FloatFactory(23, 11, RoundingMode.RNE).typ
    val field = Field("f", t)()
    val p1_decl = LocalVarDecl("three", Ref)()
    val p1_ref = p1_decl.localVar
    val p2_decl = LocalVarDecl("lol", SetType(t))()
    val p2_ref= p2_decl.localVar
    val fieldAcc = FieldAccess(p1_ref, field)()
    val perm = FieldAccessPredicate(fieldAcc, FullPerm()())()
    val element_in_param = AnySetContains(fieldAcc, p2_ref)()

    val getPerm = Inhale(perm)()
    val assume = Inhale(element_in_param)()
    val assert = Assert(element_in_param)()
    val body = if (success) Seq(getPerm, assume, assert) else Seq(getPerm, assert)
    (wrapInProgram(body, Seq(p1_decl, p2_decl), Seq(), fields = Seq(field)), assert)
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

    val first_float = SMTFuncApp(to_fp, Seq(SMTFuncApp(from_int, Seq(IntLit(first)()))()))()
    val second_float = SMTFuncApp(to_fp, Seq(SMTFuncApp(from_int, Seq(IntLit(second)()))()))()
    val result_float = SMTFuncApp(to_fp, Seq(SMTFuncApp(from_int, Seq(IntLit(result)()))()))()

    val zero_float = SMTFuncApp(to_fp, Seq(SMTFuncApp(from_int, Seq(IntLit(0)()))()))()

    val addition = SMTFuncApp(fp_add, Seq(first_float, second_float))()
    val result_addition = SMTFuncApp(fp_add, Seq(result_float, if (success) zero_float else first_float))()

    val equality = SMTFuncApp(fp_eq, Seq(addition, result_addition))()
    val assert = Assert(equality)()
    (wrapInProgram(Seq(assert), Seq(), Seq()), assert)
  }

  def generateBvOpTest(success: Boolean) : (Program, Assert) = {
    val bv23 = BVFactory(23)
    val from_int = bv23.from_int("toBV23")
    val two_lit = IntLit(2)()
    val three_lit = IntLit(3)()
    val one_lit = IntLit(1) ()
    val two = SMTFuncApp(from_int, Seq(two_lit))()
    val three = SMTFuncApp(from_int, Seq(three_lit))()
    val one = SMTFuncApp(from_int, Seq(one_lit))()
    val result_decl = LocalVarDecl("three", bv23.typ)()
    val result_ref = result_decl.localVar
    val assign = LocalVarAssign(result_ref, if (success) three else one)()
    val xor = bv23.xor("xorBV23")
    val xor_app = SMTFuncApp(xor, Seq(one, two))()
    val equality1 = EqCmp(result_ref, xor_app)()
    val assertion1 = Assert(equality1)()
    (wrapInProgram(Seq(assign, assertion1), Seq(), Seq(result_decl)), assertion1)
  }

  def wrapInProgram(stmts: Seq[Stmt], params: Seq[LocalVarDecl], vars: Seq[LocalVarDecl], fields: Seq[Field] = Seq()): Program = {
    val block = Seqn(stmts, vars)()
    val method = Method("test", params, Seq(), Seq(), Seq(), Some(block))()
    Program(Seq(), fields, Seq(), Seq(), Seq(method), Seq())()
  }

  val verifier : Verifier

  override def beforeAll(configMap: ConfigMap) {
    verifier.parseCommandLine(Seq("dummy.vpr"))
    verifier.start()
  }

  override def afterAll(configMap: ConfigMap) {
    verifier.stop()
  }

  test("typeCombinationSuccess") {
    val (prog, assertNode) = generateTypeCombinationTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("typeCombinationFail") {
    val (prog, assertNode) = generateTypeCombinationTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(assertNode, _, _))) => true
      case _ => false
    })
  }

  test("fieldTypeSuccess") {
    val (prog, assertNode) = generateFieldTypeTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("fieldTypeFail") {
    val (prog, assertNode) = generateFieldTypeTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(assertNode, _, _))) => true
      case _ => false
    })
  }

  test("bvOpSuccess") {
    val (prog, assertNode) = generateBvOpTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("bvOpFail") {
    val (prog, assertNode) = generateBvOpTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(assertNode, _, _))) => true
      case _ => false
    })
  }

  test("floatOpSuccess") {
    val (prog, assertNode) = generateFloatOpTest(true)
    val res  = verifier.verify(prog)
    assert(res == Success)
  }

  test("floatOpFail") {
    val (prog, assertNode) = generateFloatOpTest(false)
    val res  = verifier.verify(prog)
    assert(res match {
      case Failure(Seq(AssertFailed(assertNode, _, _))) => true
      case _ => false
    })
  }

}
