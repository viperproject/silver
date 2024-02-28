package viper.silver.plugin.standard.smoke

import fastparse.P
import viper.silver.ast._
import viper.silver.ast.utility.ViperStrategy
import viper.silver.cfg.silver.SilverCfg
import viper.silver.cfg.silver.SilverCfg.SilverBlock
import viper.silver.parser.FastParser
import viper.silver.plugin.standard.refute.Refute
import viper.silver.plugin.{ParserPluginTemplate, SilverPlugin}

import scala.annotation.unused
import scala.collection.mutable.ListBuffer

class SmokeDetectionPlugin(@unused reporter: viper.silver.reporter.Reporter,
                           @unused logger: ch.qos.logback.classic.Logger,
                           @unused config: viper.silver.frontend.SilFrontendConfig,
                           fp: FastParser) extends SilverPlugin with ParserPluginTemplate {

  import fp.{ParserExtension, lineCol, _file}
  import viper.silver.parser.FastParserCompanion.{PositionParsing, reservedKw}

  /** Parser for `unreachable` statements. */
  def unreachable[$: P]: P[PUnreachable] =
    P(P(PUnreachableKeyword) map PUnreachable.apply).pos

  /** Add `unreachable` to the parser. */
  override def beforeParse(input: String, isImported: Boolean): String = {
    // Add new keyword
    ParserExtension.addNewKeywords(Set(PUnreachableKeyword))
    // Add new parser to the precondition
    ParserExtension.addNewStmtAtEnd(unreachable(_))
    input
  }

  override def beforeVerify(input: Program): Program = {
    var refuteId = 0

    // Add `refute false` at end of each method body
    val transformedMethods = input.methods.map(method => {
      val bodyWithRefute = if (method.body.isEmpty) method.body else
        Option(Seqn(method.body.toSeq :+ refuteFalse(method.pos, refuteId), Seq())(method.pos))

      Method(method.name, method.formalArgs, method.formalReturns, method.pres,
        method.posts, bodyWithRefute)(method.pos, method.info, method.errT)
    })

    // Add `refute false` after each inhale, at end of each loop body, at end of each if/else branch and before each goto
    val methodsWithRefutes = transformedMethods.map(method => {
      ViperStrategy.Slim({
        case i@Inhale(expr) if i.info.getUniqueInfo[Synthesized.type].isEmpty =>
          refuteId += 1
          appendRefuteFalse(Inhale(expr)(i.pos, Synthesized), i.pos, refuteId)
        case w@While(cond, invs, body) =>
          refuteId += 1
          While(cond, invs, appendRefuteFalse(body, body.pos, refuteId))(w.pos)
        case i@If(cond, thn, els) =>
          var thnWithRefute: Seqn = thn
          var elsWithRefute: Seqn = els

          if (thn.ss.nonEmpty) {
            refuteId += 1
            thnWithRefute = appendRefuteFalse(thn, thn.pos, refuteId)
          }

          if (els.ss.nonEmpty) {
            refuteId += 1
            elsWithRefute = appendRefuteFalse(els, els.pos, refuteId)
          }

          If(cond, thnWithRefute, elsWithRefute)(i.pos)
        case g@Goto(target) if g.info.getUniqueInfo[Synthesized.type].isEmpty =>
          refuteId += 1
          Seqn(Seq(refuteFalse(g.pos, refuteId), Goto(target)(g.pos, Synthesized)), Seq())(g.pos)
      }).execute[Method](method)
    })

    // Remove all `refute false` statements which are inside of control-flow branch marked as unreachable
    val methodsWithoutUnreachableRefutes = methodsWithRefutes.map(method => {
      val cfg = method.toCfg(simplify = false)
      val result = collectRefutesToKeep(cfg)

      ViperStrategy.Slim({
        case r@Refute(_) =>
          val info = r.info.getUniqueInfo[SmokeDetectionInfo]

          if (info.isDefined &&
            !result._1.contains(info.get.id) && // not marked reachable
            result._2.contains(info.get.id)) { // actually considered when traversing CFG
            Seqn(Seq(), Seq())(r.pos) // remove refute statement
          } else {
            r
          }
        case u@Unreachable() =>
          Seqn(Seq(), Seq())(u.pos)
      }).execute[Method](method)
    })

    Program(input.domains, input.fields, input.functions, input.predicates, methodsWithoutUnreachableRefutes,
      input.extensions)(input.pos, input.info, input.errT)
  }

  /**
   * Construct a [[Seqn]] consisting of `stmt` followed by a `refute false` statement with position `pos`.
   * The `Refute` instance will have the ID `refuteId`.
   *
   * @param stmt     the statement at the beginning of the sequence
   * @param pos      the position of the resulting [[Seqn]] instance
   * @param refuteId the ID of the `refute false` statement at the end of the sequence
   * @return a [[Seqn]] instance consisting of `stmt` and a `refute false` statement
   */
  private def appendRefuteFalse(stmt: Stmt, pos: Position, refuteId: Int): Seqn = {
    Seqn(Seq(stmt, refuteFalse(pos, refuteId)), Seq())(pos)
  }

  /**
   * Construct a `refute false` statement with position `pos` and ID `id`.
   *
   * @param pos the position of the resulting [[Refute]] instance
   * @param id  the ID of the `refute false` statement
   * @return a [[Refute]] instance with with the `exp` set to `false` and the given position and ID
   */
  private def refuteFalse(pos: Position, id: Int): Refute = {
    Refute(FalseLit()(pos))(pos, SmokeDetectionInfo(id))
  }

  /**
   * Construct a list of the IDs of all `refute false` statements that are not marked unreachable.
   *
   * @param cfg the control-flow graph of a method
   * @return a list of the IDs of the reachable `refute false` statements and a list of the IDs of the `refute false`
   *         statements that were encountered when traversing the control-flow graph
   */
  private def collectRefutesToKeep(cfg: SilverCfg): (List[Int], List[Int]) = {
    val refutesToKeep = ListBuffer[Int]()
    val seenRefutes = ListBuffer[Int]()
    collectRefutesToKeepUntilExit(cfg, cfg.entry, cfg.exit.toSeq, ListBuffer[SilverBlock](),
      refutesToKeep, seenRefutes, unreachable = false)
    (refutesToKeep.toList, seenRefutes.toList)
  }

  /**
   * Recursively construct a list of the IDs of all `refute false` statements that are not marked as unreachable on the
   * path from the node `current` to one of the nodes in `exits` in the control-flow graph `cfg`.
   *
   * @param cfg           the control-flow graph
   * @param current       the currently considered node in the control-flow graph
   * @param exits         a list of potential exit nodes of the currently considered subgraph
   * @param seen          a list of all nodes of the control-flow graph that have already been visited
   * @param refutesToKeep the list of the IDs of all `refute false` statements which are not on an unreachable path
   * @param seenRefutes the list of the IDs of all `refute false` statements that were already considered
   * @param unreachable   indicates whether the current node is on a path marked as unreachable
   * @return `true` if some part of the path from the `current` node to one of the `exits` is unreachable, otherwise `false`
   */
  private def collectRefutesToKeepUntilExit(cfg: SilverCfg,
                                            current: SilverBlock,
                                            exits: Seq[SilverBlock],
                                            seen: ListBuffer[SilverBlock],
                                            refutesToKeep: ListBuffer[Int],
                                            seenRefutes: ListBuffer[Int],
                                            unreachable: Boolean): Boolean = {
    seen += current
    val elements = current.elements

    var unreachableSuccessors = unreachable

    for (elem <- elements) {
      val leftElem = elem.left.getOrElse(null)

      leftElem match {
        case _: Unreachable =>
          // Encountered `unreachable` statement -> successors of current node are unreachable
          unreachableSuccessors = true
        case refute: Refute if refute.exp.isInstanceOf[FalseLit] =>
          // Encountered `refute false` statement -> add ID to list if it is reachable
          val info = refute.info.getUniqueInfo[SmokeDetectionInfo]

          if (info.isDefined) {
            val id = info.get.id

            if (!unreachableSuccessors) {
              refutesToKeep += id
            }

            seenRefutes += id
          }
        case _ =>
      }
    }

    if (exits.contains(current)) {
      // Considered whole path
      return unreachableSuccessors
    }

    val successors = cfg.successors(current).filter(s => !seen.contains(s))
    val joinPointMap = cfg.joinPoints

    if (joinPointMap.contains(current)) {
      // Current node is branch point
      val joinPoint = joinPointMap(current)
      val joinPointPredecessors = cfg.predecessors(joinPoint)
      var allBranchesUnreachable = true

      for (elem <- successors) {
        val unreachableBranch = collectRefutesToKeepUntilExit(cfg, elem, joinPointPredecessors, seen,
          refutesToKeep, seenRefutes, unreachableSuccessors)
        if (!unreachableBranch) {
          allBranchesUnreachable = false
        }
      }

      // If all paths from the branch point to the join point contain an `unreachable` statement, the code following
      // the joint point (including the join point) is also unreachable.
      return collectRefutesToKeepUntilExit(cfg, joinPoint, exits, seen, refutesToKeep, seenRefutes, allBranchesUnreachable)
    }

    // Current node is no branch point -> collect Refute IDs for successor node
    successors.forall(s => collectRefutesToKeepUntilExit(cfg, s, exits, seen, refutesToKeep, seenRefutes, unreachableSuccessors))
  }
}

/**
 * An info used to mark AST nodes (more specifically, `refute false` statements) as used in smoke detection,
 * also assigning a unique identifier to it.
 *
 * @param id the ID of the node
 */
case class SmokeDetectionInfo(id: Int) extends Info {
  override def comment: Seq[String] = Seq(s"`refute false` #$id")

  override def isCached: Boolean = false
}
