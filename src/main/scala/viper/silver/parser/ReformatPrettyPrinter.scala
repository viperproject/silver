// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2024 ETH Zurich.

/**
 * The idea behind how the reformatter works is as follows:
 *
 * Firstly, it's based on the parse AST (PProgram) and not the Viper AST (Program), which actually already has
 * a pretty printing functionality. But it's not suitable for actual reformatting for a couple of reasons:
 * At the point where we generate the AST, it's already processed in a way that makes it unsuitable for formatting.
 * For examples, macros will be expanded, imports will be inlined, and most importantly, information about whitespaces
 * and comments is completely discarded, and so on. Because of this, using the parse AST as a basis for the formatter
 * is just more sensible.
 *
 * The steps are as follows:
 * - We first build the parse AST for a specific Viper file.
 * - Then, we iterate over each node in the tree and turn it into a list of RNodes. A RNode is very similar
 *   to the primitives provided by `PrettyPrintPrimitives`, the reason we don't convert directly into a pretty
 *   print tree is that we need to perform some preprocessing on whitespaces, which is just much easier to do
 *   if we store everything in an intermediate representation.
 * - Whenever we hit a leaf node, we get all comments and whitespaces that appear from the last position
 *   we stored up to that leaf node, and print them. This is necessary to preserve comments and certain kinds of
 *   newlines, which is important when reformatting a file.
 * - Once we have our finalized list of RNodes, we convert them into a pretty print tree and print that tree,
 *   similarly to how it's done for the pretty printer for the Viper AST.
 */

package viper.silver.parser

import fastparse.Parsed
import viper.silver.ast
import viper.silver.ast.HasLineColumn
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.parser.FastParserCompanion.pTrivia

import scala.collection.mutable.ArrayBuffer

// A reformattable node.
trait RNode {
  def isNil: Boolean
}
trait RCommentFragment
trait RWhitespace extends RNode with RCommentFragment

object RNode {
  def rn(): Seq[RNode] = Seq()
  def rne(l: Seq[RNode]): Seq[RNode] = Seq(RNest(l))
  def rg(l: Seq[RNode]): Seq[RNode] = Seq(RGroup(l))
  def rt(text: String): Seq[RNode] = Seq(RText(text))
  def rs(): Seq[RNode] = Seq(RSpace())
  def rl(): Seq[RNode] = Seq(RLine())
  def rlb(): Seq[RNode] = Seq(RLineBreak())
}

case class RText(text: String) extends RNode {
  override def isNil: Boolean = text.isEmpty
}

case class RTrivia(l: Seq[RCommentFragment]) extends RNode {
  override def isNil: Boolean = l.isEmpty

  def hasComment(): Boolean = l.exists(_ match {
    case RComment(_) => true
    case _ => false
  })

  def trimmedLw(): RTrivia = l.headOption match {
    case Some(_: RWhitespace) => RTrivia(l.tail)
    case _ => this
  }

  def replacedLw(r: RWhitespace): RTrivia = l.headOption match {
    case Some(_: RWhitespace) => RTrivia(r +: l.tail)
    case _ => this
  }
}

case class RComment(comment: PComment) extends RCommentFragment

case class RNest(l: Seq[RNode]) extends RNode {
  override def isNil: Boolean = l.forall(_.isNil)
}

case class RGroup(l: Seq[RNode]) extends RNode {
  override def isNil: Boolean = l.forall(_.isNil)
}

case class RSpace() extends RWhitespace with RCommentFragment {
  override def isNil: Boolean = false
}

case class RLine() extends RWhitespace {
  override def isNil: Boolean = false
}

case class RLineBreak() extends RWhitespace with RCommentFragment {
  override def isNil: Boolean = false
}

case class RDLineBreak() extends RWhitespace with RCommentFragment {
  override def isNil: Boolean = false
}

trait RReformatPad {
  def leftPad: Option[RNode] = None
  def rightNest: Boolean = false
  def rightGroup: Boolean = false
  def rightPad: Option[RNode] = None
}

trait RLeftSpace extends RReformatPad {
  override def leftPad: Option[RNode] = Some(RSpace())
}
trait RRightSpace extends RReformatPad {
  override def rightPad: Option[RNode] = Some(RSpace())
}
trait RRightGroupLine extends RReformatPad {
  override def rightGroup: Boolean = true
  override def rightPad: Option[RNode] = Some(RLine())
}
trait RRightNestGroupLine extends RRightGroupLine {
  override def rightNest: Boolean = true
}

object RReformatPad {
  def get(n: PNode): Option[RReformatPad] = n match {
    case n: RReformatPad => Some(n)
    case _ => None
  }
  def leftPad(n: PNode): Option[RNode] = get(n).flatMap(_.leftPad)
  def rightNest(n: PNode): Boolean = get(n).exists(_.rightNest)
  def rightGroup(n: PNode): Boolean = get(n).exists(_.rightGroup)
  def rightPad(n: PNode): Option[RNode] = get(n).flatMap(_.rightPad)
}

trait REndLineBreak {
  def endLinebreak: Boolean = true
}

object REndLineBreak {
  def endLinebreak(n: PNode): Boolean = n match {
    case n: REndLineBreak => n.endLinebreak
    case _ => false
  }
}

sealed trait ReformatPrettyPrinterBase extends FastPrettyPrinterBase {
  override val defaultIndent = 4
  override val defaultWidth = 75
}

case class ReformatterContext(val program: String, val offsets: Option[Seq[Int]]) {
  // Store the last position we have processed, so we don't include certain trivia
  // twice.
  var currentOffset: Int = 0

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets.get(p.line - 1);
    row + p.column - 1
  }

  // Get all trivia for a node position. The first position
  // is the start position of the node (i.e. the end position when getting
  // the trivia) and the second position is the end position of the node (i.e.
  // the value `currentOffset` should be updated to).
  def getTrivia(pos: (ast.Position, ast.Position)): Option[RTrivia] = {
    (pos._1, pos._2, offsets) match {
      case (p: HasLineColumn, q: HasLineColumn, Some(_)) => {
        val p_offset = getByteOffset(p);
        val q_offset = getByteOffset(q);
        getTriviaByByteOffset(p_offset, q_offset)
      }
      case _ => None
    }
  }

  def getTriviaByByteOffset(end: Int, updateOffset: Int): Option[RTrivia] = {
    if (currentOffset <= end) {
      val str = program.substring(currentOffset, end);
      currentOffset = updateOffset

      fastparse.parse(str, pTrivia(_)) match {
        case Parsed.Success(value, _) => {
          // Create a list of deduplicated whitespaces, and comments.
          val trivia = ArrayBuffer[RCommentFragment]()
          var newlines = 0
          var spaces = 0

          val addTrivia = () => if (newlines > 1) {
            trivia += RDLineBreak()
          } else if (newlines > 0) {
            trivia += RLineBreak()
          } else if (spaces > 0) {
            trivia += RSpace()
          }

          for (t <- value) {
            t match {
              case p: PComment => {
                addTrivia()
                trivia += RComment(p)

                newlines = 0
                spaces = 0

                // In case we had a line comment, add the linebreak
                // manually, since it was stripped in PComment.
                if (p.trimmed) {
                  newlines += 1
                }
              }
              case _: PNewLine => newlines += 1
              case _: PSpace => spaces += 1
              case _ =>
            }
          }

          addTrivia()

          trivia match {
            case t if t.isEmpty => None
            case t => Some(RTrivia(t.toSeq))
          }
        }
        case _: Parsed.Failure => None
      }
    } else {
      None
    }
  }
}

class PrettyPrintContext {
  var whitespace: Option[RWhitespace] = None

  def register(w: RWhitespace): Unit = {
    whitespace match {
      case None => whitespace = Some(w)
      // If we already have a linebreak, it should not be overwritten e.g. by a space,
      // and special handling applies in case we want a double line break.
      case Some(_: RLineBreak) => w match {
        case _: RLineBreak => whitespace = Some(RDLineBreak())
        case _: RDLineBreak => whitespace = Some(RDLineBreak())
        case _ =>
      }
      case Some(_) => whitespace = Some(w)
    }
  }
}

object ReformatPrettyPrinter extends ReformatPrettyPrinterBase {
  def reformatAny(parent: PNode, children: Iterator[Any])(implicit ctx: ReformatterContext, f: PartialFunction[PNode, Seq[RNode]] = PartialFunction.empty): Seq[RNode] = {
    reformatSubnodes(children.flatMap(PNode.nodes(parent, _)))
  }

  def reformatSubnodes(subnodes: Iterator[PNode], endLinebreak: Boolean = false)(implicit ctx: ReformatterContext, f: PartialFunction[PNode, Seq[RNode]] = PartialFunction.empty): Seq[RNode] = {
    import scala.collection.mutable.ArrayBuffer
    val nodes = ArrayBuffer[RNode]()
    while (subnodes.hasNext) {
      val n = subnodes.next()
      RReformatPad.leftPad(n).foreach(nodes += _)

      nodes ++= n.reformatSuper

      n match {
        case n: RReformatPad if (n.rightNest || n.rightGroup) => {
          var others = reformatSubnodes(subnodes)
          n.rightPad.foreach(ws => others = ws +: others)

          (n.rightNest, n.rightGroup) match {
            case (true, true) => nodes += RNest(Seq(RGroup(others)))
            case (true, false) => nodes += RNest(others)
            case (false, true) => nodes += RGroup(others)
            case (false, false) => ???
          }
          return nodes.toSeq
        }
        case n: RReformatPad => {
          n.rightPad.foreach(nodes += _)
        }
        case _ =>
      }
    }
    if (endLinebreak) {
      nodes += RLineBreak()
    }
    nodes.toSeq
  }

  def showNode(p: PNode)(implicit f: PartialFunction[PNode, Seq[RNode]] = PartialFunction.empty): String = {
    implicit val ctx = ReformatterContext("", None)
    val reformat = p.reformatSuper

    val pc = new PrettyPrintContext()
    super.pretty(defaultWidth, showList(reformat, pc))
  }
  
  def showProgram(p: PProgram): String = {
    implicit val ctx = ReformatterContext(p.rawProgram, Some(p.offsets))

    val pc = new PrettyPrintContext()
    val mainProgram = p.reformatSuper
    // Don't forget the trivia after the last program node, i.e. trailing comments!
    val trailing = ctx.getTriviaByByteOffset(ctx.program.length, ctx.program.length).toSeq
    val finalProgram = (mainProgram ++ trailing).filter(!_.isNil)
    super.pretty(defaultWidth, showList(finalProgram, pc))
  }

  def showList(p: Seq[RNode], pc: PrettyPrintContext): Cont = {
    def hasLeadingLwNode(l: Seq[RNode]): Boolean = l.headOption.map(_ match {
      case p: RGroup => hasLeadingLwNode(p.l)
      case p: RNest => hasLeadingLwNode(p.l)
      case _: RWhitespace => true
      case _ => false
    }).getOrElse(false)

    def showWhitespace(w: RWhitespace): Cont = {
      w match {
        case RSpace() => space
        case RLine() => line
        case RLineBreak() => linebreak
        case RDLineBreak() => linebreak <> linebreak
      }
    }
    
    def flushWhitespace(pc: PrettyPrintContext): Cont = {
      val cont = pc.whitespace.map(showWhitespace(_)).getOrElse(nil)
      pc.whitespace = None
      
      cont
    }

    def showTrivia(p: RTrivia): Cont = {
      if (p.l.isEmpty) {
        nil
      } else {
        p.l.map(t => t match {
          case w: RWhitespace => showWhitespace(w)
          case p: RComment => text(p.comment.str)
        }).reduce((acc, n) => acc <> n)
      };
    }

    def showNode(p: RNode, pc: PrettyPrintContext): Cont = {
      p match {
        case w: RWhitespace => {
          pc.register(w)

          nil
        }
        case RText(t: String) => {
          flushWhitespace(pc) <> text(t)
        }
        case t: RTrivia => {
          val trivia = if (t.hasComment()) {
            // If we already had a whitespace as part of formatting the program, we might have to
            // trim the leading whitespace from the trivia.
            pc.whitespace match {
              case None => showTrivia(t)
              // If we want a double linebreak and we already had a linebreak, replace it with a simple linebreak.
              case Some(_: RLineBreak) => if (t.l.headOption == Some(RDLineBreak())) {
                  showTrivia(t.replacedLw(RLineBreak()))
                } else {
                  showTrivia(t.trimmedLw())
                }
              // If we want a space and already had a space, do not write double space, trim it instead.
              case Some(_: RSpace) => if (t.l.headOption == Some(RSpace())) {
                showTrivia(t.trimmedLw())
              } else {
                showTrivia(t)
              }
              case Some(_) => showTrivia(t.trimmedLw())
            }
          } else {
            val newlines = t.l.map(_ match {
              case RLineBreak() => 1
              case RDLineBreak() => 2
              case _ => 0
            }).sum

            pc.whitespace match {
              case Some(_: RLineBreak) => if (newlines > 1) linebreak else nil
              case _ => nil
            }
          }
          
          flushWhitespace(pc) <> trivia
        }
        case RGroup(l: Seq[RNode]) => {
          val lw = flushWhitespace(pc) 
          val grouped = group(showList(l, pc))
          
          if (hasLeadingLwNode(l)) {
            grouped
          } else {
            // Only add the leading whitespace if the current group doesn't start with one.
            lw <> grouped
          }
        }
        case RNest(l: Seq[RNode]) => {
          val lw = flushWhitespace(pc)
          val nested = nest(defaultIndent, showList(l, pc))
          
          if (hasLeadingLwNode(l)) {
            nested
          } else {
            // Only add the leading whitespace if the current nesting doesn't start with one.
            lw <> nested
          }
        }
      }
    }

    var reformatted = nil
    for (n <- p) {
      reformatted = reformatted <> showNode(n, pc)
    }
    reformatted
  }
}
