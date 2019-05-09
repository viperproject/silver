// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.Paths
import scala.collection.mutable
import TestHelpers.{FileComparisonHelper, MockSilFrontend}
import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.ast.utility.rewriter._
import viper.silver.ast.utility._

class RegexTests extends FunSuite with FileComparisonHelper {
  test("Sharing") {
    val shared = FalseLit()()
    val sharedAST = And(Not(shared)(), shared)()

    val t = TreeRegexBuilder.context[Node, Int](_ + _, math.max , 0)
    val strat = t &> c[Not](_ => 1) > n.r[FalseLit] |-> { case (FalseLit(), c) => if(c.c == 1) TrueLit()() else FalseLit()()}

    val res = strat.execute[Exp](sharedAST)

    // Check that both FalseLits were differently transformed
    res match {
      case And(Not(t1), t2) =>
        assert(t1 == TrueLit()())
        assert(t2 == FalseLit()())
      case _ => assert(false)
    }
  }

  test("Performance_BinomialHeap") {
    val fileName = "transformations/Performance/BinomialHeap"

    // Regular expression
    val t = TreeRegexBuilder.simple[Node]

    // Arbitrary regex to observe how much the matching slows down the program
    val strat = t &> n[Program] >> iC[Method](_.bodyOrAssumeFalse) >> n.r[Implies] |-> { case (i:Implies) => Or(Not(i.left)(), i.right)()}

    val frontend = new MockSilFrontend

    val fileRes = getClass.getResource(fileName + ".sil")
    assert(fileRes != null, s"File $fileName not found")
    val file = Paths.get(fileRes.toURI)
    var targetNode: Node = null

    frontend.translate(file) match {
      case (Some(p), _) => targetNode = p
      case (None, errors) => fail("Problem with program: " + errors)
    }

//    time(strat.execute[Program](targetNode))
    strat.execute[Program](targetNode)
  }


  test("DisjunctionToInhaleExhaleTests") {
    val filePrefix = "transformations/DisjunctionToInhaleExhale/"
    val files = Seq("simple", "nested", "functions")

    val frontend = new MockSilFrontend
    files foreach (fileName => {
      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      val fileRef = getClass.getResource(filePrefix + fileName + "Ref.sil")
      assert(fileRes != null, s"File $filePrefix$fileName not found")
      assert(fileRef != null, s"File $filePrefix$fileName Ref not found")
      val file = Paths.get(fileRes.toURI)
      val ref = Paths.get(fileRef.toURI)

      var targetNode: Program = null
      var targetRef: Program = null

      frontend.translate(file) match {
        case (Some(p), _) => targetNode = p
        case (None, errors) => fail("Problem with program: " + errors)
      }

      // We use for NonDet a function that has name NonDet(i) where i is number of arguments
      def NonDet(_vars: Seq[LocalVarDecl]): Exp = {
        /* 2017-04-28 Malte:
         *   The order of the `vars` is nondeterministic, which sometimes makes the comparison
         *   with the expected output program fail.
         *   As a work around, we order the variables, see below.
         *   One source of non-determinism seems to be the use of `SeqLike.distinct` (see below),
         *   which internally uses a `HashSet`, which presumably does not have a deterministic
         *   traversal order.
         *   Another source seems to be the RegexStrategy itself: even without the use of
         *   distinct (i.e. just using `x ++ y`), the final sequence of variables passed to
         *   `NonDet` seems to be in nondeterministic order.
         */
        val vars = _vars.map(_.localVar).sortBy(_.name)
        if (vars.isEmpty) return TrueLit()()
        val func: Function = targetNode.functions.find(_.name == "NonDet" + vars.size).get
        FuncApp(func, vars)()
      }

      // Regular expression
      val t = TreeRegexBuilder.context[Node, Seq[LocalVarDecl]](
        _ ++ _,
        (x,y) => (x ++ y).distinct,
        Seq.empty)

      val strat = (
        t &> c[QuantifiedExp]( _.variables).** >> n.r[Or]
          |-> { case (o:Or, c) =>
                  InhaleExhaleExp(
                    CondExp(
                      NonDet(c.c), o.left, o.right)(), c.noRec[Or](o))()
              })

      frontend.translate(ref) match {
        case (Some(p), _) => targetRef = p
        case (None, errors) => fail("Problem with program: " + errors)
      }

      val res = strat.execute[Program](targetNode)

      val obtainedOutput = res.toString()
      val expectedOutput = targetRef.toString()

      assert(obtainedOutput == expectedOutput,
             s"""Transformation of program $fileRes did not yield expected program $fileRef:
                |------Got ------
                |$obtainedOutput
                |--- Expected ---
                |$expectedOutput
              """.stripMargin)
    })
  }

  test("ComplexMatching") {
    val filePrefix = "transformations/ComplexMatching/"
    val files = Seq("simple", "complex")

    // Regular expression
    val t = TreeRegexBuilder.context[Node, Int](_ + _, math.max, 0)
    val strat = t &> iC[Method](_.bodyOrAssumeFalse, _.name == "here") >> (n[Inhale] | n[Exhale]) >> (c[Or]( _ => 1 )  | c[And]( _ => 1)).* >> n.r[LocalVar]((v:LocalVar) => v.typ == Int && v.name.contains("x")) |-> { case (n:LocalVar, c) => IntLit(c.c)(n.pos, n.info, n.errT)}

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend)}
  }

  test("PresentationSlides") {

    val filePrefix = "transformations/PresentationSlides/"
    val files = Seq("simple")

    // Regular expression
    val t = TreeRegexBuilder.simple[Node]
    val strat = t &> iC[Implies](_.right) > n[Or].+ >> n.r[TrueLit] |-> { case _: TrueLit => FalseLit()()}

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend)}
  }


  test("ImplicationToDisjunctionTests") {
    val filePrefix = "transformations/ImplicationsToDisjunction/"
    val files = Seq("simple", "nested", "traverseEverything")


    // Regular expression
    val t = TreeRegexBuilder.simple[Node]
    val strat = t &> n.r[Implies] |-> { case (i:Implies) => Or(Not(i.left)(), i.right)()}

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend) }
  }

  test("WhileToIfAndGoto") {
    val filePrefix = "transformations/WhileToIfAndGoto/"
    val files = Seq("simple", "nested")

    // Regular expression
    val t = TreeRegexBuilder.simple[Node]
    var count = 0
    val strat = t &> n.r[While] |-> {
      case (w: While) =>
        val invars: Exp = w.invs.reduce((x: Exp, y: Exp) => And(x, y)())
        count = count + 1
        Seqn(Seq(
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(Not(w.cond)(w.cond.pos, w.cond.info), Seqn(Seq(Goto("skiploop" + count)(w.pos, w.info)), Seq())(w.pos, w.info), Seqn(Seq(), Seq())(w.pos, w.info))(w.pos, w.info),
          Label("loop" + count, Seq(TrueLit()()))(w.pos, w.info),
          w.body,
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(w.cond, Seqn(Seq(Goto("loop" + count)(w.pos, w.info)), Seq())(w.pos, w.info), Seqn(Seq(), Seq())(w.pos, w.info))(w.pos, w.info),
          Label("skiploop" + count, Seq(TrueLit()()))(w.pos, w.info)
        ), Seq())(w.pos, w.info)
    }

    val frontend = new MockSilFrontend
    files foreach { fileName: String => {
      count = 0
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }


  test("ManyToOneAssert") {
    val filePrefix = "transformations/ManyToOneAssert/"
    val files = Seq("simple", "interrupted", "nested", "nestedBlocks")
    var accumulator: mutable.ListBuffer[Exp] = mutable.ListBuffer.empty[Exp]

    val t = TreeRegexBuilder.ancestor[Node]
    val strat = t &> n.r[Assert] |-> {
      case (a: Assert, c) =>
        accumulator += a.exp
        c.next match {
          case Some(Assert(_)) =>
            Seqn(Seq(), Seq())()
          case _ =>
            val result = Assert(accumulator.reduceRight(And(_, _)()))()
            accumulator.clear()
            result
        }
    }

    val frontend = new MockSilFrontend
    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }


  test("UnfoldedChildren") {
    val filePrefix = "transformations/UnfoldedChildren/"
    val files = Seq("fourAnd")

    val t = TreeRegexBuilder.ancestor[Node]
    val strat = t &> n.P[FuncApp]( _.funcname == "fourAnd") > n.r[Exp] |-> { case (e:Exp, c) => if(c.siblings.contains(FalseLit()())) FalseLit()() else e }

    val frontend = new MockSilFrontend
    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }

  test("MethodCallDesugaring") {
    // Careful: Don't use old inside postcondition. It is not yet supported. maybe I will update the testcase (or not)
    val filePrefix = "transformations/MethodCallDesugaring/"
    val files = Seq("simple", "withArgs", "withArgsNRes", "withFields")

    val frontend = new MockSilFrontend


    val t = TreeRegexBuilder.ancestor[Node]
    val strat = t &> n.r[MethodCall] |-> {
      case (m: MethodCall, anc) =>
        // Get method declaration
        val mDecl = anc.ancestorList.head.asInstanceOf[Program].methods.find(_.name == m.methodName).get

        // Create an exhale statement for every precondition and replace parameters with arguments
        var replacer: Map[LocalVar, Exp] = mDecl.formalArgs.zip(m.args).map(x => x._1.localVar -> x._2).toMap
        val replaceStrat = StrategyBuilder.Slim[Node]({
          case l: LocalVar => if (replacer.contains(l)) replacer(l) else l
        })
        val exPres = mDecl.pres.map(replaceStrat.execute[Exp](_)).map(x => Exhale(x)(m.pos, m.info))

        // Create an inhale statement for every postcondition, replace parameters with arguments and replace result parameters with receivers
        val replacedArgs = mDecl.posts.map(replaceStrat.execute[Exp](_))
        replacer = mDecl.formalReturns.zip(m.targets).map(x => x._1.localVar -> x._2).toMap
        val inPosts = replacedArgs.map(replaceStrat.execute[Exp](_)).map(x => Inhale(x)(m.pos, m.info))

        Seqn(exPres ++ inPosts, Seq())(m.pos, m.info)
    }

    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }


  test("CopyPropagation") {
    val filePrefix = "transformations/CopyPropagation/"
    val files = Seq("simple", "complex")

    val frontend = new MockSilFrontend

    val map = collection.mutable.Map.empty[LocalVar, BigInt]
    val collect = ViperStrategy.Slim({
      case p: Program => map.clear(); p // Reset map at start
      case ass@LocalVarAssign(l: LocalVar, i: IntLit) => map += (l -> i.i); ass
    }) recurseFunc { case l: LocalVarAssign => Seq(l.rhs) }

    val replace = ViperStrategy.Slim({
      case l: LocalVar =>
        map.get(l) match {
          case None => l
          case Some(i: BigInt) => IntLit(i)(l.pos, l.info)
        }
    })

    val t = TreeRegexBuilder.simple[Node]
    val fold = t &> n.r[BinExp] |-> {
      case root@Add(i1: IntLit, i2: IntLit) => IntLit(i1.i + i2.i)(root.pos, root.info)
      case root@Sub(i1: IntLit, i2: IntLit) => IntLit(i1.i - i2.i)(root.pos, root.info)
      case root@Div(i1: IntLit, i2: IntLit) => if (i2.i != 0) IntLit(i1.i / i2.i)(root.pos, root.info) else root
      case root@Mul(i1: IntLit, i2: IntLit) => IntLit(i1.i * i2.i)(root.pos, root.info)
      case root@Or(b1: BoolLit, b2: BoolLit) => BoolLit(b1.value || b2.value)(root.pos, root.info)
      case root@And(b1: BoolLit, b2: BoolLit) => BoolLit(b1.value && b2.value)(root.pos, root.info)
      case root@EqCmp(b1: BoolLit, b2: BoolLit) => BoolLit(b1.value == b2.value)(root.pos, root.info)
      case root@EqCmp(i1: IntLit, i2: IntLit) => BoolLit(i1.i == i2.i)(root.pos, root.info)
    }

    val combined = (collect + replace) || fold.repeat

    files foreach { name => executeTest(filePrefix, name, combined, frontend) }
  }
}
