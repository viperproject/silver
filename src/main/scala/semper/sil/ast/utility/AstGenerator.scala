package semper.sil.ast.utility

import semper.sil.ast.While
import semper.sil.ast.Block
import semper.sil.ast.Stmt
import semper.sil.ast.TerminalBlock
import semper.sil.ast.NormalBlock
import semper.sil.ast.ConditionalBlock
import semper.sil.ast.LoopBlock
import semper.sil.ast.Seqn
import semper.sil.ast.ConditionalBlock
import semper.sil.ast.Goto
import semper.sil.ast.Label
import semper.sil.ast.If

// TODO Totally unfinished
object AstGenerator {
  
  def toAst(block: Block): Stmt = {
    val surroundingLoops = calculateSurroundingLoops(block)
    statementize(translateList(continuation(block, Set(), surroundingLoops, None), Set(), surroundingLoops)._1)
  }
    
  def calculateSurroundingLoops(block: Block, surroundingLoop: Option[LoopBlock] = None, knownSurroundingLoops: Map[Block, Option[LoopBlock]] = Map()): Map[Block, Option[LoopBlock]] = {
    if (knownSurroundingLoops.contains(block))  {
      knownSurroundingLoops
    } else {
      val loops1 = knownSurroundingLoops + (block -> surroundingLoop)
      block match {
        case ConditionalBlock(_, _, thn, els) => {
          val loops2 = calculateSurroundingLoops(els, surroundingLoop, loops1)
          calculateSurroundingLoops(thn, surroundingLoop, loops2)
        }
        case NormalBlock(_, succ) => calculateSurroundingLoops(succ, surroundingLoop, loops1)
        case TerminalBlock(_) => loops1
        case b @ LoopBlock(body, _, _, _, succ) => {
          val loops2 = calculateSurroundingLoops(succ, surroundingLoop, loops1)
          calculateSurroundingLoops(body, Some(b), loops2)
        }
      }
    }
  }
  
  case class BranchInformation(thn: List[Block], els: List[Block], continuation: List[Block])
  
  // Remove this
  val partsCache = scala.collection.mutable.HashMap[Block, BranchInformation]()

  /** Finds both branches and the continuation of a conditional block. */
  private def extractParts(block: ConditionalBlock, usedBlocks: Set[Block], surroundingLoops: Map[Block, Option[LoopBlock]]) = {
    if (partsCache.contains(block)) {
      partsCache(block)
    } else {
      val thenContinuation = continuation(block.thn, usedBlocks + block, surroundingLoops, surroundingLoops(block))
      val elseContinuation = continuation(block.els, usedBlocks + block, surroundingLoops, surroundingLoops(block))
      val (revContinuationPairs, revBranches) = thenContinuation.reverse.zip(elseContinuation.reverse).span(a => a._1 eq a._2)
      val revContinuation = revContinuationPairs.unzip._1
      val (revThen, revElse) = revBranches.unzip
      val branchInfo = BranchInformation(revThen.reverse, revElse.reverse, revContinuation.reverse)
      partsCache.put(block, branchInfo)
      branchInfo
    }
  }
  
  /** Returns true iff the first loop is equal to or inside the second loop */
  private def loopIsInside(first: Option[LoopBlock], second: Option[LoopBlock], surroundingLoops: Map[Block, Option[LoopBlock]]): Boolean = {
    if (first == second) {
      true
    } else first match {
      case None => false
      case Some(loop) => loopIsInside(surroundingLoops(loop), second, surroundingLoops)
    }
  }
  
  /** Returns the list of one node and all successors in the AST without gotos or loop bodies and overjumping
   * branches of conditionals. */
  private def continuation(block: Block, usedBlocks: Set[Block], surroundingLoops: Map[Block, Option[LoopBlock]], surroundingLoop: Option[LoopBlock]): List[Block] = {
    if (usedBlocks contains block) {
      throw new RuntimeException("Backward gotos are not allowed.")
    } else if (surroundingLoops(block) != surroundingLoop) {
      if (loopIsInside(surroundingLoop, surroundingLoops(block), surroundingLoops)) {
        Nil
      } else {
        throw new RuntimeException("Jumping into a loop with a goto is not allowed.")
      }
    } else block match {
      case b: ConditionalBlock => b :: extractParts(b, usedBlocks + b, surroundingLoops).continuation
      case b: TerminalBlock => List(b)
      case b @ LoopBlock(body, _, _, _, succ) => b :: continuation(succ, usedBlocks + b, surroundingLoops, surroundingLoop)
      case b @ NormalBlock(_, succ) => b :: continuation(succ, usedBlocks + b, surroundingLoops, surroundingLoop)
    }
  }
  
  // TODO Remove this
  private val labels = scala.collection.mutable.HashMap[Block, String]()
  
  /** Creates a statement from a list of statements by either using the unique element or a Seqn. */
  def statementize(stmts: List[Stmt]) = stmts match {
    case List(stmt) => stmt
    case _ => Seqn(stmts)()
  }
  
  private def translateList(blocks: List[Block], usedBlocks: Set[Block], surroundingLoops: Map[Block, Option[LoopBlock]]): (List[Stmt], Set[Block]) = blocks match {
    case Nil => (Nil, Set())
    case (b @ NormalBlock(stmt, succ)) :: Nil if (surroundingLoops(b) != surroundingLoops(succ)) => {
      // Goto at the end of the continuation
      val (stmts, used) = translate(b, usedBlocks, surroundingLoops)
      val label = UniqueNames.createUnique("label")
      (stmts :+ Goto(label)(), used)
    }
    case block :: rest => {
      val (stmts, used) = translate(block, usedBlocks, surroundingLoops)
      val (restStmts, restUsed) = translateList(rest, used ++ usedBlocks, surroundingLoops)
      (stmts ++ restStmts, used ++ restUsed)
    }
  }
  
  private def translate(block: Block, usedBlocks: Set[Block], surroundingLoops: Map[Block, Option[LoopBlock]]): (List[Stmt], Set[Block]) = {
    if (usedBlocks contains block) {
      throw new RuntimeException("Invalid Goto")
    } else {
      val (translated, used) = block match {
        case TerminalBlock(stmt) => (List(stmt), Set(block))
        case NormalBlock(stmt, _) => (List(stmt), Set(block))
        case b @ ConditionalBlock(stmt, cond, thn, els) => {
          val BranchInformation(thn, els, continuation) = extractParts(b, usedBlocks, surroundingLoops)
          val (thenAst, thenUsed) = translateList(thn, usedBlocks + block, surroundingLoops)
          val (elseAst, elseUsed) = translateList(els, usedBlocks + block, surroundingLoops)
          val translatedIf = If(cond, statementize(thenAst), statementize(elseAst))()
          (List(stmt, translatedIf), thenUsed ++ elseUsed + block)
        }
        case b @ LoopBlock(body, cond, invs, locals, succ) => {
          val used1 = usedBlocks + block
          val (translatedBody, used2) = translateList(continuation(body, used1, surroundingLoops, Some(b)), used1, surroundingLoops)
          val translatedLoop = While(cond, invs, locals, statementize(translatedBody))()
          (List(translatedLoop), used2)
        }
      }
      if (labels contains block) {
        (Label(labels(block))() :: translated, used)
      } else {
        (translated, used)
      }
    }
  }
  
}