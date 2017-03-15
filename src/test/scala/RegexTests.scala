/**
  * Created by simonfri on 14.02.2017.
  *
 * This Source Code Form is subject to the terms of the Mozilla Public
 * License, v. 2.0. If a copy of the MPL was not distributed with this
 * file, You can obtain one at http://mozilla.org/MPL/2.0/.
*/

import java.nio.file.{Path, Paths}

import org.scalatest.{FunSuite, Matchers}
import viper.silver.ast._
import viper.silver.ast.utility.Rewriter._
import viper.silver.ast.utility._
import viper.silver.frontend.{SilFrontend, TranslatorState}
import viper.silver.verifier.AbstractError

import scala.collection.mutable
import scala.language.implicitConversions


class RegexTests extends FunSuite {

  test("Sharing") {
    val shared = FalseLit()()
    val sharedAST = And(Not(shared)(), shared)()

    val t = TreeRegexBuilder.context[Node, Int](_ + _, _ > _, 0)
    val strat = t &> c[Not](_ => 1) > n.r[FalseLit] |-> { case (FalseLit(), c) => if(c.c == 1) TrueLit()() else FalseLit()()}

    val res = strat.execute[Exp](sharedAST)

    // Check that both true lits are no longer of the same instance
    res match {
      case And(Not(t1), t2) => {
        assert(t1 == TrueLit()())
        assert(t2 == FalseLit()())
      }
      case _ => assert(false)
    }
  }

  test("Performance_BinomialHeap") {
    val fileName = "transformations\\Performance\\BinomialHeap"

    // Regular expression
    val t = TreeRegexBuilder.simple[Node]

    // Arbitrary regex to observe how much the matching slows down the program
    val strat = t &> n[Program] >> iC[Method](_.body) >> n.r[Implies] |-> { case (i:Implies) => Or(Not(i.left)(), i.right)()}

    val frontend = new DummyFrontend

    val fileRes = getClass.getResource(fileName + ".sil")
    assert(fileRes != null, s"File $fileName not found")
    val file = Paths.get(fileRes.toURI)
    var targetNode: Node = null

    frontend.translate(file) match {
      case (Some(p), _) => targetNode = p
      case (None, errors) => println("Problem with program: " + errors)
    }


    val res = time(strat.execute[Program](targetNode))

    assert(true)
  }


  test("DisjunctionToInhaleExhaleTests") {
    val filePrefix = "transformations\\DisjunctionToInhaleExhale\\"
    val files = Seq("simple", "nested", "functions")

    val frontend = new DummyFrontend
    files foreach { fileName: String => {
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
        case (None, errors) => println("Problem with program: " + errors)
      }

      // We use for NonDet a function that has name NonDet(i) where i is number of arguments
      def NonDet(vars: Seq[LocalVarDecl]): Exp = {
        if (vars.isEmpty) return TrueLit()()
        val func: Function = targetNode.functions.find(_.name == "NonDet" + vars.size).get
        FuncApp(func, vars.map { x => x.localVar })()
      }

      // Regular expression
      val t = TreeRegexBuilder.context[Node, Seq[LocalVarDecl]]( _ ++ _ , _.size > _.size, Seq.empty[LocalVarDecl])
      val strat = t &> c[QuantifiedExp]( _.variables).** >> n.r[Or] |-> { case (o:Or, c) => InhaleExhaleExp(CondExp(NonDet(c.c), o.left, o.right)(), c.noRec[Or](o))() }

      frontend.translate(ref) match {
        case (Some(p), _) => targetRef = p
        case (None, errors) => println("Problem with program: " + errors)
      }

      val res = strat.execute[Program](targetNode)
      //  println("Old: " + targetNode.toString())
      println("New: " + res.toString())
      println("Reference: " + targetRef.toString())
      assert(res.toString() == targetRef.toString(), "Files are not equal")
    }
    }
  }

  test("ComplexMatching") {
    val filePrefix = "transformations\\ComplexMatching\\"
    val files = Seq("simple", "complex")

    // Regular expression
    val t = TreeRegexBuilder.context[Node, Int](_ + _, _ > _, 0)
    val strat = t &> iC[Method](_.body, _.name == "here") >> (n[Inhale] | n[Exhale]) >> (c[Or]( _ => 1 )  | c[And]( _ => 1)).* >> n.r[LocalVar]((v:LocalVar) => v.typ == Int && v.name.contains("x")) |-> { case (n:LocalVar, c) => IntLit(c.c)(n.pos, n.info, n.errT)}

    val frontend = new DummyFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend)}
  }

  test("PresentationSlides") {

    val filePrefix = "transformations\\PresentationSlides\\"
    val files = Seq("simple")

    // Regular expression
    val t = TreeRegexBuilder.simple[Node]
    val strat = t &> iC[Implies](_.right) > n[Or].+ >> n.r[TrueLit] |-> { case t:TrueLit => FalseLit()()}

    val frontend = new DummyFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend)}

  }


  test("ImplicationToDisjunctionTests") {
    val filePrefix = "transformations\\ImplicationsToDisjunction\\"
    val files = Seq("simple", "nested", "traverseEverything")


    // Regular expression
    val t = TreeRegexBuilder.simple[Node]
    val strat = t &> n.r[Implies] |-> { case (i:Implies) => Or(Not(i.left)(), i.right)()}

    val frontend = new DummyFrontend
    files foreach { name => executeTest(filePrefix, name, strat, frontend) }
  }

  test("WhileToIfAndGoto") {
    val filePrefix = "transformations\\WhileToIfAndGoto\\"
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
          If(Not(w.cond)(w.cond.pos, w.cond.info), Goto("skiploop" + count)(w.pos, w.info), Seqn(Seq())(w.pos, w.info))(w.pos, w.info),
          Label("loop" + count, Seq(TrueLit()()))(w.pos, w.info),
          w.body,
          Assert(invars)(w.invs.head.pos, w.invs.head.info),
          If(w.cond, Goto("loop" + count)(w.pos, w.info), Seqn(Seq())(w.pos, w.info))(w.pos, w.info),
          Label("skiploop" + count, Seq(TrueLit()()))(w.pos, w.info)
        ))(w.pos, w.info)
    }

    val frontend = new DummyFrontend
    files foreach { fileName: String => {
      count = 0
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }


  test("ManyToOneAssert") {
    val filePrefix = "transformations\\ManyToOneAssert\\"
    val files = Seq("simple", "interrupted", "nested", "nestedBlocks")
    var accumulator: mutable.ListBuffer[Exp] = mutable.ListBuffer.empty[Exp]

    val t = TreeRegexBuilder.ancestor[Node]
    val strat = t &> n.r[Assert] |-> {
      case (a: Assert, c) =>
        accumulator += a.exp
        c.next match {
          case Some(Assert(_)) =>
            Seqn(Seq())()
          case _ =>
            val result = Assert(accumulator.reduceRight(And(_, _)()))()
            accumulator.clear()
            result
        }
    }

    val frontend = new DummyFrontend
    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }


  test("UnfoldedChildren") {
    val filePrefix = "transformations\\UnfoldedChildren\\"
    val files = Seq("fourAnd")

    val t = TreeRegexBuilder.ancestor[Node]
    val strat = t &> n.P[FuncApp]( _.funcname == "fourAnd") > n.r[Exp] |-> { case (e:Exp, c) => if(c.siblings.contains(FalseLit()())) FalseLit()() else e }

    val frontend = new DummyFrontend
    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }

  test("MethodCallDesugaring") {
    // Careful: Don't use old inside postcondition. It is not yet supported. maybe I will update the testcase (or not)
    val filePrefix = "transformations\\MethodCallDesugaring\\"
    val files = Seq("simple", "withArgs", "withArgsNRes", "withFields")

    val frontend = new DummyFrontend


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

        Seqn(exPres ++ inPosts)(m.pos, m.info)
    }

    files foreach { fileName: String => {
      executeTest(filePrefix, fileName, strat, frontend)
    }
    }
  }


  test("CopyPropagation") {
    val filePrefix = "transformations\\CopyPropagation\\"
    val files = Seq("simple", "complex")

    val frontend = new DummyFrontend

    val map = collection.mutable.Map.empty[LocalVar, BigInt]
    val collect = ViperStrategy.Slim({
      case p: Program => map.clear(); p // Reset map at start
      case ass@LocalVarAssign(l: LocalVar, i: IntLit) => map += (l -> i.i); ass
    }) recurseFunc { case l: LocalVarAssign => Seq(false, true) }

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

  def executeTest(filePrefix: String, fileName: String, strat: StrategyInterface[Node], frontend: DummyFrontend): Unit = {

    val fileRes = getClass.getResource(filePrefix + fileName + ".sil")
    assert(fileRes != null, s"File $filePrefix$fileName not found")
    val file = Paths.get(fileRes.toURI)
    var targetNode: Node = null
    var targetRef: Node = null

    frontend.translate(file) match {
      case (Some(p), _) => targetNode = p
      case (None, errors) => println("Problem with program: " + errors)
    }
    val res = strat.execute[Program](targetNode)

    val fileRef = getClass.getResource(filePrefix + fileName + "Ref.sil")
    assert(fileRef != null, s"File $filePrefix$fileName Ref not found")

    val ref = Paths.get(fileRef.toURI)
    frontend.translate(ref) match {
      case (Some(p), _) => targetRef = p
      case (None, errors) => println("Problem with program: " + errors)
    }

    //  println("Old: " + targetNode.toString())
    println("New: " + res.toString)
    println("Reference: " + targetRef.toString())
    assert(res.toString == targetRef.toString(), "Files are not equal")
  }

  // From: http://biercoff.com/easily-measuring-code-execution-time-in-scala/
  def time[R](block: => R): R = {
    val t0 = System.nanoTime()
    val result = block    // call-by-name
    val t1 = System.nanoTime()
    println("Elapsed time: " + (t1 - t0) + "ns")
    result
  }

  class DummyFrontend extends SilFrontend {
    def createVerifier(fullCmd: _root_.scala.Predef.String) = ???

    def configureVerifier(args: Seq[String]) = ???

    def translate(silverFile: Path): (Option[Program], Seq[AbstractError]) = {
      _verifier = None
      _state = TranslatorState.Initialized

      reset(silverFile) //
      translate()

      //println(s"_program = ${_program}") /* Option[Program], set if parsing and translating worked */
      //println(s"_errors = ${_errors}")   /*  Seq[AbstractError], contains errors, if encountered */

      (_program, _errors)
    }
  }

}
