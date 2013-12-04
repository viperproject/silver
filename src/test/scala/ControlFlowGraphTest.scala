package semper.sil

import org.scalatest.{BeforeAndAfter, FunSuite}
import semper.sil.ast._
import semper.sil.ast.utility.ControlFlowGraph
import java.lang.RuntimeException
import java.nio.file.FileSystems
import org.scalatest.matchers.ShouldMatchers

class ControlFlowGraphTest extends FunSuite with BeforeAndAfter with ShouldMatchers {
  // Some AST nodes that are useful to construct test CFGs
  val emptyStmt = Seqn(Seq.empty)()
  val nonEmptyStmt = Assert(TrueLit()())()
  val trueLit = TrueLit()()
  val falseLit = FalseLit()()

  def assertEq(b1: Block, b2: Block) =
    assert(ControlFlowGraph.eq(b1, b2), s"Expected $b2, got $b1")

  def assertDisjoint(b1: Block, b2: Block) = {
    val blocks1 = ControlFlowGraph.collectBlocks(b1).toSet
    val blocks2 = ControlFlowGraph.collectBlocks(b2).toSet
    assert (blocks1.intersect(blocks2).isEmpty)
  }

  def assertEqAndDisjoint(b1: Block, b2: Block) = {
    assertEq(b1, b2)
    assertDisjoint(b1, b2)
  }

  {
    // Tests that operate on a simple CFG:
    // NormalBlock(assert true) -> NormalBlock() -> TerminalBlock()
    val end = TerminalBlock(emptyStmt)
    val middle = NormalBlock(emptyStmt, end)
    val begin = NormalBlock(nonEmptyStmt, middle)

    val differentEnd = TerminalBlock(nonEmptyStmt)
    val differentMiddle = NormalBlock(nonEmptyStmt, differentEnd)

    test("Block Removal in Linear CFG") {
      // Remove the first block
      assertEqAndDisjoint(begin transform {
        case b @ NormalBlock(stmt, succ) if b == begin => succ
      }, middle)

      // Remove the middle block
      assertEqAndDisjoint(begin transform {
        case b @ NormalBlock(stmt, succ) if b == middle => succ
      }, NormalBlock(begin.stmt, TerminalBlock(end.stmt)))

      // Remove the terminal block (turning the middle block into a terminal block)
      assertEqAndDisjoint(begin transform {
        case b @ NormalBlock(stmt, succ) if b == middle => TerminalBlock(stmt)
      }, NormalBlock(begin.stmt, TerminalBlock(middle.stmt)))

      // Remove all but the terminal block
      assertEqAndDisjoint(begin transform {
        case b @ NormalBlock(stmt, succ) => end
      }, TerminalBlock(end.stmt))
    }

    test("Transformation with Cycles (Invalid)") {
      intercept[RuntimeException] {
        begin.transform({
          // Cannot resolve this block due to cycle (1 block)
          case b => b
        })
      }

      intercept[RuntimeException] {
        begin.transform({
          // Cannot resolve this block due to cycle (2 blocks)
          case b if b == begin => middle
          case b if b == middle => begin
        })
      }
    }

    test("Shallow Equality of Blocks") {
      assert(ControlFlowGraph.shallowEq(end, TerminalBlock(end.stmt)))
      assert(ControlFlowGraph.shallowEq(middle, NormalBlock(middle.stmt, differentEnd)))
      assert(ControlFlowGraph.shallowEq(begin, NormalBlock(begin.stmt, differentMiddle)))

      assert(!ControlFlowGraph.shallowEq(end, differentEnd))
      assert(!ControlFlowGraph.shallowEq(middle, differentMiddle))
    }

    test("Equality of CFGs") {
      assert(ControlFlowGraph.eq(end, TerminalBlock(end.stmt)))
      assert(ControlFlowGraph.eq(middle, NormalBlock(middle.stmt, TerminalBlock(end.stmt))))

      assert(!ControlFlowGraph.eq(end, differentEnd))
      assert(!ControlFlowGraph.eq(middle, differentMiddle))
      assert(!ControlFlowGraph.eq(middle, NormalBlock(middle.stmt, differentEnd)))
    }

    test("Collect Blocks") {
      assert(ControlFlowGraph.collectBlocks(begin) == Seq(begin, middle, end))
      assert(ControlFlowGraph.collectBlocks(middle) == Seq(middle, end))
      assert(ControlFlowGraph.collectBlocks(end) == Seq(end))
    }

    test("Shallow Copy of Blocks") {
      val beginCopy = ControlFlowGraph.shallowCopy(begin).asInstanceOf[NormalBlock]
      assert(ControlFlowGraph.shallowEq(begin, beginCopy))
      assert(begin.succ == beginCopy.succ) // Not disjoint
    }
  }

  {
    // Tests that operate on a more complex CFG:
    // ConditionalBlock(true):
    //  - FreshReadPermBlock with TerminalBlock body
    //  - LoopBlock(false) with body: NormalBlock -> TerminalBlock
    //
    // The FreshReadPermBlock and LoopBlock have the same TerminalBlock as successor
    val exitBlock = TerminalBlock(emptyStmt)

    val loopBlockBody = NormalBlock(nonEmptyStmt, TerminalBlock(emptyStmt))
    val loopBlock = LoopBlock(loopBlockBody, falseLit, Seq.empty, Seq.empty, exitBlock)()

    val frpBlockBody = TerminalBlock(emptyStmt)
    val frpBlock = FreshReadPermBlock(Seq.empty, frpBlockBody, exitBlock)

    val condBlock = ConditionalBlock(emptyStmt, trueLit, frpBlock, loopBlock)
    val cfg = condBlock

    test("Nop Transformation") {
      val newCfg = ControlFlowGraph.transform(cfg)
      assertEq(cfg, newCfg)
      assertDisjoint(cfg, newCfg)
    }

    test("ConditionalBlock Simplification") {
      assertEqAndDisjoint(cfg.transform({
        case ConditionalBlock(stmt, TrueLit(), thn, els) => NormalBlock(stmt, thn)
      }), NormalBlock(condBlock.stmt, frpBlock))
    }

    test("LoopBlock Simplification") {
      assertEqAndDisjoint(cfg.transform({
        case LoopBlock(body, FalseLit(), invs, locals, succ) => succ
      }), ConditionalBlock(condBlock.stmt, condBlock.cond, condBlock.thn, exitBlock))
    }
  }

  test("Shallow Copy") {
    // LoopBlock has a second argument list. Assert that it is copied as well.
    val dummyPath = FileSystems.getDefault.getPath("foo.scala")
    val loopBlock = LoopBlock(
      body = TerminalBlock(emptyStmt),
      cond = trueLit,
      invs = Seq.empty,
      locals = Seq.empty,
      succ = TerminalBlock(emptyStmt))(
      pos = SourcePosition(dummyPath, 21, 42))

    val loopBlockCopy = loopBlock.copyShallow().asInstanceOf[LoopBlock]
    loopBlockCopy.body should equal (loopBlock.body)
    loopBlockCopy.pos should equal (loopBlock.pos)
  }
}