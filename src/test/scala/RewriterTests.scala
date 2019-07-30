// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

import java.nio.file.Paths

import TestHelpers.{FileComparisonHelper, MockSilFrontend}
import org.scalatest.FunSuite
import viper.silver.ast._
import viper.silver.ast.utility.rewriter._
import viper.silver.ast.utility._

class RewriterTests extends FunSuite with FileComparisonHelper {
  test("Performance_BinomialHeap") {
    val fileName = "transformations/Performance/BinomialHeap"

    val strat = ViperStrategy.Slim({
      case Implies(left, right) => Or(Not(left)(), right)()
    })

    val frontend = new MockSilFrontend

    val fileRes = getClass.getResource(fileName + ".sil")
    assert(fileRes != null, s"File $fileName not found")
    val file = Paths.get(fileRes.toURI)
    var targetNode: Node = null

    frontend.translate(file) match {
      case (Some(p), _) => targetNode = p
      case (None, errors) => fail("Problem with program: " + errors)
    }

    strat.execute[Program](targetNode)
  }

  test("Sharing") {
    val shared = FalseLit()()
    val sharedAST = And(Not(shared)(), shared)()

    val strat = ViperStrategy.CustomContext[Int]({ case (FalseLit(), c) => if (c == 1) TrueLit()() else FalseLit()() }, 0, { case (Not(_), i) => i + 1 })

    val res = strat.execute[Exp](sharedAST)

    // Check that both true lits are no longer of the same instance
    res match {
      case And(Not(t1), t2) =>
        assert(t1 == TrueLit()())
        assert(t2 == FalseLit()())
      case _ => assert(false)
    }
  }


  // same as the test above, but with a Context rather than SimpleContext strategy
  test("Sharing (richer context, unused)") {
     val shared = FalseLit()()
     val sharedAST = And(Not(shared)(), shared)()

     val strat = ViperStrategy.Context[Int]({ case (FalseLit(), c) => if (c.c == 1) TrueLit()() else FalseLit()() }, 0, { case (Not(_), i) => i + 1 })

     val res = strat.execute[Exp](sharedAST)

     // Check that both true lits are no longer of the same instance
     res match {
       case And(Not(t1), t2) =>
         assert(t1 == TrueLit()())
         assert(t2 == FalseLit()())
      case _ => assert(false)
    }
  }


  test("QuantifiedPermissions") {
    val filePrefix = "transformations/QuantifiedPermissions/"
    val files = Seq("simple", "allCases")

    val strat = ViperStrategy.Ancestor({
      case (f@Forall(_, _, Implies(_, r)), _) if r.isPure =>
        f
      case (f@Forall(decls, triggers, i@Implies(li, And(l, r))), ass) =>
        val forall = Forall(decls, triggers, Implies(li, r)(i.pos, i.info))(f.pos, f.info)
        And(Forall(decls, triggers, Implies(li, l)(i.pos, i.info))(f.pos, f.info), ass.noRec[Forall](forall))(f.pos, f.info)
      case (f@Forall(decls, triggers, i@Implies(li, Implies(l, r))), _) if l.isPure =>
        Forall(decls, triggers, Implies(And(li, l)(i.pos, i.info), r)(i.pos, i.info))(f.pos, f.info)
    })

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend) }

  }

  test("DisjunctionToInhaleExhaleTests") {
    val filePrefix = "transformations/DisjunctionToInhaleExhale/"
    val files = Seq("simple", "nested", "functions")

    val frontend = new MockSilFrontend
    files foreach {
      fileName: String => {
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
        def NonDet(vars: Seq[LocalVarDecl]): Exp = {
          if (vars.isEmpty) return TrueLit()()
          val func: Function = targetNode.functions.find(_.name == "NonDet" + vars.size).get
          FuncApp(func, vars.map { x => x.localVar })()
        }

        val strat = ViperStrategy.Context[Seq[LocalVarDecl]]({
          case (o@Or(l, r), c) =>
            InhaleExhaleExp(CondExp(NonDet(c.c), l, r)(), c.noRec[Or](o))()
        }, Seq.empty, {
          case (q: QuantifiedExp, c) => c ++ q.variables
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
      }
    }
  }

  test("ImplicationToDisjunctionTests") {
    val filePrefix = "transformations/ImplicationsToDisjunction/"
    val files = Seq("simple", "nested", "traverseEverything")



    // Create new strategy. Parameter is the partial function that is applied on all nodes
    val strat = ViperStrategy.Slim({
      case Implies(left, right) => Or(Not(left)(), right)()
    })

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend) }
  }

  test("WhileToIfAndGoto") {
    val filePrefix = "transformations/WhileToIfAndGoto/"
    val files = Seq("simple", "nested")

    // Example of how to transform a while loop into if and goto
    // Keeping metadata is awful when creating multiple statements from a single one and we need to think about this case, but at least it is possible
    var count = 0
    val strat = ViperStrategy.Slim({
      case w: While =>
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
    })

    val frontend = new MockSilFrontend
    files foreach {
      fileName: String => {
        count = 0
        executeTest(filePrefix, fileName, strat, frontend)
      }
    }
  }

  test("ManyToOneAssert") {
    val filePrefix = "transformations/ManyToOneAssert/"
    val files = Seq("simple", "interrupted", "nested", "nestedBlocks")

    val strat = ViperStrategy.Ancestor({
      case (a: Assert, c) =>
        c.previous match {
          case Some(Assert(_)) => Seqn(Seq(), Seq())() // If previous node is assertion we go to noop
          case _ =>
            // Otherwise we take all following assertions and merge their expressions into one
            c.successors.takeWhile({
              // Take all following assertions
              case Assert(_) => true
              case _ => false
            }).collect({ case i: Assert => i }) match {
              // Collect works as a cast to list of assertion since take while does not do this
              case Seq() => a
              case as =>
                // Merge in case of multiple assertions
                val foldedExpr = as collect { case assertion => assertion.exp } reduceRight { (l, r) => And(l, r)() }
                Assert(And(a.exp, foldedExpr)())(a.pos, a.info)
            }
        }
    })

    val frontend = new MockSilFrontend
    files foreach {
      fileName: String => executeTest(filePrefix, fileName, strat, frontend)
    }
  }

  test("ManyToOneAssert2") {
    val filePrefix = "transformations/ManyToOneAssert/"
    val files = Seq("simple", "interrupted", "nested", "nestedBlocks")

    var accumulator: List[Exp] = List.empty[Exp]
    val strat = ViperStrategy.Ancestor({
      case (a: Assert, c) =>
        accumulator ++= List(a.exp)
        c.next match {
          case Some(Assert(_)) =>
            Seqn(Seq(), Seq())()
          case _ =>
            val result = Assert(accumulator.reduceRight(And(_, _)()))()
            accumulator = List.empty[Exp]
            result
        }
    })

    val frontend = new MockSilFrontend
    files foreach {
      fileName: String => executeTest(filePrefix, fileName, strat, frontend)
    }
  }

  test("FoldConstants") {
    val filePrefix = "transformations/FoldConstants/"
    val files = Seq("simple", "complex")


    val strat = ViperStrategy.Slim({
      case root@Add(i1: IntLit, i2: IntLit) => IntLit(i1.i + i2.i)(root.pos, root.info)
      case root@Sub(i1: IntLit, i2: IntLit) => IntLit(i1.i - i2.i)(root.pos, root.info)
      case root@Div(i1: IntLit, i2: IntLit) => if (i2.i != 0) IntLit(i1.i / i2.i)(root.pos, root.info) else root
      case root@Mul(i1: IntLit, i2: IntLit) => IntLit(i1.i * i2.i)(root.pos, root.info)
    }) traverse Traverse.BottomUp

    val frontend = new MockSilFrontend
    files foreach {
      fileName: String => executeTest(filePrefix, fileName, strat, frontend)
    }

  }

  test("UnfoldedChildren") {
    val filePrefix = "transformations/UnfoldedChildren/"
    val files = Seq("fourAnd")


    val strat: StrategyInterface[Node] = ViperStrategy.Ancestor({
      case (e: Exp, c) => c.parent match {
        case f: FuncApp => if (f.funcname == "fourAnd" && c.siblings.contains(FalseLit()())) {
          FalseLit()(e.pos, e.info)
        } else {
          e
        }
        case _ => e
      }
    }) traverse Traverse.BottomUp

    val frontend = new MockSilFrontend
    files foreach {
      fileName: String => executeTest(filePrefix, fileName, strat, frontend)
    }
  }

  test("CountAdditions") {
    val filePrefix = "transformations/CountAdditions/"
    val filesAndResults = Seq(("simple", 3), ("nested", 10), ("traverseEverything", 12))

    val query = new Query[Node, Int]({
      case _: Add => 1
    }) neutralElement 0 accumulate { (s: Seq[Int]) => s.sum }

    val frontend = new MockSilFrontend

    filesAndResults foreach ((tuple) => {
      val fileName = tuple._1
      val result = tuple._2

      val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
      assert(fileRes != null, s"File $filePrefix$fileName not found")
      val file = Paths.get(fileRes.toURI)

      var targetNode: Node = null
      frontend.translate(file) match {
        case (Some(p), _) => targetNode = p
        case (None, errors) =>
          fail(s"Problem with program $file: $errors")
      }
      val res = query.execute(targetNode)

      assert(res == result, "Results are not equal")
    })
  }

  test("MethodCallDesugaring") {
    // Careful: Don't use old inside postcondition. It is not yet supported. maybe I will update the testcase
    val filePrefix = "transformations/MethodCallDesugaring/"
    val files = Seq("simple", "withArgs", "withArgsNRes", "withFields")

    val frontend = new MockSilFrontend

    val strat = ViperStrategy.Ancestor({
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
    }, Traverse.Innermost)

    files foreach {
      fileName: String => executeTest(filePrefix, fileName, strat, frontend)
    }
  }

  test("ImplicationSimplification") {
    val filePrefix = "transformations/ImplicationSimplification/"
    val files = Seq("simple", "complex")

    // Create new strategy. Parameter is the partial function that is applied on all nodes
    val strat = ViperStrategy.Slim({
      case i@Implies(left, right) => Or(Not(left)(i.pos, i.info), right)(i.pos, i.info)
    }) traverse Traverse.BottomUp

    val strat2 = ViperStrategy.Slim({
      case o@Or(Not(f: FalseLit), right) => Or(TrueLit()(f.pos, f.info), right)(o.pos, o.info)
      case o@Or(Not(f: TrueLit), right) => Or(FalseLit()(f.pos, f.info), right)(o.pos, o.info)
      case o@Or(left, Not(f: FalseLit)) => Or(left, TrueLit()(f.pos, f.info))(o.pos, o.info)
      case o@Or(left, Not(f: TrueLit)) => Or(left, FalseLit()(f.pos, f.info))(o.pos, o.info)
    })

    val strat3 = ViperStrategy.Slim({
      case o@Or(_: TrueLit, _) => TrueLit()(o.pos, o.info)
      case o@Or(_, _: TrueLit) => TrueLit()(o.pos, o.info)
    })

    val strat4 = ViperStrategy.Slim({
      case Assert(_: TrueLit) => Seqn(Seq(), Seq())()
    })


    val combined = strat < (strat2 + strat3) || strat4

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, combined, frontend) }
  }

  test("IfThenElseTest") {
    val filePrefix = "transformations/IfThenElseTest/"
    val files = Seq("complex")

    // Create new strategy. Replace even integers with variable x and odd integers with variable y
    val strat = ViperStrategy.Slim({
      case i:IntLit if i.i % 2 == 0 => IntLit(i.i)()
    }) traverse Traverse.BottomUp recurseFunc {
      case _: LocalVarAssign => Seq() // Don't modify anything during assignments
    }

    val strat2 = ViperStrategy.Slim({
      case i:IntLit => LocalVar("x", i.typ)()
    })

    val strat3 = ViperStrategy.Slim({
      case i:IntLit => LocalVar("y", i.typ)()
    })

    val combined = strat ? strat2 | strat3

    val frontend = new MockSilFrontend
    files foreach { name => executeTest(filePrefix, name, combined, frontend) }
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

    val fold = ViperStrategy.Slim({
      case root@Add(i1: IntLit, i2: IntLit) => IntLit(i1.i + i2.i)(root.pos, root.info)
      case root@Sub(i1: IntLit, i2: IntLit) => IntLit(i1.i - i2.i)(root.pos, root.info)
      case root@Div(i1: IntLit, i2: IntLit) => if (i2.i != 0) IntLit(i1.i / i2.i)(root.pos, root.info) else root
      case root@Mul(i1: IntLit, i2: IntLit) => IntLit(i1.i * i2.i)(root.pos, root.info)
      case root@Or(b1: BoolLit, b2: BoolLit) => BoolLit(b1.value || b2.value)(root.pos, root.info)
      case root@And(b1: BoolLit, b2: BoolLit) => BoolLit(b1.value && b2.value)(root.pos, root.info)
      case root@EqCmp(b1: BoolLit, b2: BoolLit) => BoolLit(b1.value == b2.value)(root.pos, root.info)
      case root@EqCmp(i1: IntLit, i2: IntLit) => BoolLit(i1.i == i2.i)(root.pos, root.info)
    }) traverse Traverse.TopDown // Do this top down such that we need to iterate

    val combined = (collect + replace) || fold.repeat

    files foreach { name => executeTest(filePrefix, name, combined, frontend) }
  }

  test("No infinite recursive rewrite through referential equality") {
    // This test rewrites the following program:
    // method m()
    // {
    //   var y: Int
    //
    //   y := 4
    //   y := 4
    // }
    //
    // Into this one:
    // method m()
    // {
    //   var y: Int
    //
    //   assert y != 4
    //   y := 4
    //   assert y != 4
    //   y := 4
    // }
    //
    // This test is enforcing the fix of issue 231, where the second assignment wasn't being replaced because it
    // was mistaken by first one, blacklisted to avoid infinite rewrite recursion.

    // Initial program
    val localVarDecl = LocalVarDecl("y", Int)()
    val assign1 = LocalVarAssign(LocalVar("y", Int)(), IntLit(4)())()
    val assign2 = LocalVarAssign(LocalVar("y", Int)(), IntLit(4)())()
    val methodBefore = Method("m", Seq(), Seq(), Seq(), Seq(), Some(Seqn(Seq(assign1, assign2), Seq(localVarDecl))()))()
    val programBefore = Program(Seq(), Seq(), Seq(), Seq(), Seq(methodBefore), Seq())()

    // Program transformer or rewriter
    val programTransformed = StrategyBuilder.Ancestor[Node]({
      case (l@LocalVarAssign(lhs, rhs), ctx) =>
        Seqn(
          Seq(
            Assert(NeCmp(lhs, rhs)())(),
            ctx.noRec[LocalVarAssign](l)
          ),
          Seq()
        )()
    }).execute[Program](programBefore)

    // Final program to compare with transformed program
    val assert1 = Assert(NeCmp(LocalVar("y", Int)(), IntLit(4)())())()
    val methodAfter = Method("m", Seq(), Seq(), Seq(), Seq(), Some(Seqn(Seq(Seqn(Seq(assert1, assign1), Seq())(), Seqn(Seq(assert1, assign2), Seq())()), Seq(localVarDecl))()))()
    val programAfter = Program(Seq(), Seq(), Seq(), Seq(), Seq(methodAfter), Seq())()

    // Compare transformed program with expected program
    assert(programAfter === programTransformed)
  }
}
