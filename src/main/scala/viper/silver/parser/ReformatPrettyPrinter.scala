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
import viper.silver.parser.RNode._

import scala.collection.mutable.ArrayBuffer

// A reformattable node.
trait RNode {
  def isNil: Boolean
}
trait RCommentFragment
trait RWhitespace extends RNode with RCommentFragment

object RNode {
  def rn(): List[RNode] = List(RNil())
  def rne(l: List[RNode]): List[RNode] = List(RNest(l))
  def rg(l: List[RNode]): List[RNode] = List(RGroup(l))
  def rt(text: String): List[RNode] = List(RText(text))
  def rs(): List[RNode] = List(RSpace())
  def rl(): List[RNode] = List(RLine())
  def rlb(): List[RNode] = List(RLineBreak())
}

case class RNil() extends RNode {
  override def isNil: Boolean = true
}

case class RText(text: String) extends RNode {
  override def isNil: Boolean = text.isEmpty
}

case class RTrivia(l: List[RCommentFragment]) extends RNode {
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
    case Some(_: RWhitespace) => RTrivia(r :: l.tail)
    case _ => this
  }
}

case class RComment(comment: PComment) extends RCommentFragment

case class RNest(l: List[RNode]) extends RNode {
  override def isNil: Boolean = l.forall(_.isNil)
}

case class RGroup(l: List[RNode]) extends RNode {
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

object RDLineBreak extends RWhitespace {
  override def isNil: Boolean = false
}

sealed trait ReformatPrettyPrinterBase extends FastPrettyPrinterBase {
  override val defaultIndent = 4
  override val defaultWidth = 75
}

trait ReformatBase {
  implicit class ContOps(dl: List[RNode]) {
    def com(dr: List[RNode]): List[RNode] =
      dl ::: dr

    def <>(dr: List[RNode]): List[RNode] =
      if (dl.forall(_.isNil)) dr else if (dr.forall(_.isNil)) dl else dl com dr

    def <+>(dr: List[RNode]): List[RNode] =
      if (dr.forall(_.isNil)) dl else if (dl.forall(_.isNil)) dr else dl ::: rs() ::: dr

    def <@>(dr: List[RNode]): List[RNode] =
      if (dr.forall(_.isNil)) dl else if (dl.forall(_.isNil)) dr else dl ::: rl() ::: dr

    def <->(dr: List[RNode]): List[RNode] =
      if (dr.forall(_.isNil)) dl else if (dl.forall(_.isNil)) dr else dl ::: rlb() ::: dr
  }
}

trait Reformattable extends ReformatBase with Where {
  def reformat(implicit ctx: ReformatterContext): List[RNode]
}

trait ReformattableExpression extends ReformatBase with PNode {
  def reformatExp(implicit ctx: ReformatterContext): List[RNode] = this match {
    case p: PLeaf => rt(p.pretty)
    case _ => ReformatPrettyPrinter.reformatNodesNoSpace(this)
  }
}

class ReformatterContext(val program: String, val offsets: Seq[Int]) {
  // Store the last position we have processed, so we don't include certain trivia
  // twice.
  var currentOffset: Int = 0

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

  // Get all trivia for a node position. The first position
  // is the start position of the node (i.e. the end position when getting
  // the trivia) and the second position is the end position of the node (i.e.
  // the value `currentOffset` should be updated to).
  def getTrivia(pos: (ast.Position, ast.Position)): RTrivia = {
    (pos._1, pos._2) match {
      case (p: HasLineColumn, q: HasLineColumn) => {
        val p_offset = getByteOffset(p);
        val q_offset = getByteOffset(q);
        getTriviaByByteOffset(p_offset, q_offset)
      }
      case _ => RTrivia(List())
    }
  }

  def getTriviaByByteOffset(end: Int, updateOffset: Int): RTrivia = {
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

          RTrivia(trivia.toList)
        }
        case _: Parsed.Failure => RTrivia(List())
      }
    } else {
      RTrivia(List())
    };
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
        case _: RLineBreak => whitespace = Some(RDLineBreak)
        case _: RDLineBreak => whitespace = Some(RDLineBreak)
      }
      case Some(_) => whitespace = Some(w)
    }
  }
}

object ReformatPrettyPrinter extends ReformatPrettyPrinterBase with ReformatBase {
  def reformatProgram(p: PProgram): String = {
    implicit val ctx = new ReformatterContext(p.rawProgram, p.offsets)

    def showWhitespace(w:RWhitespace): Cont = {
      w match {
        case RSpace() => space
        case RLine() => line
        case RLineBreak() => linebreak
        case RDLineBreak() => linebreak <> linebreak
      }
    }

    def showTrivia(p: RTrivia): Cont = {
      if (p.l.isEmpty) {
        nil
      } else {
        p.l.map(t => t match {
          case w: RWhitespace => showWhitespace(w)
          case p: RComment => text(p.comment.str)
        }).reduce((acc, n) => acc <> n)
      }
    }

    def showNode(p: RNode, pc: PrettyPrintContext): Cont = {
      p match {
        case RNil() => nil
        case w: RWhitespace => {
          pc.register(w)
          showWhitespace(w)
        }
        case RText(t: String) => {
          pc.whitespace = None
          text(t)
        }
        case t: RTrivia => {
          if (t.hasComment()) {
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
        }
        case RGroup(l: List[RNode]) => group(showList(l, pc))
        case RNest(l: List[RNode]) => nest(defaultIndent, showList(l, pc))
      }
    }

    def showList(p: List[RNode], pc: PrettyPrintContext): Cont = {
      var reformatted = nil
      for (n <- p) {
        reformatted = reformatted <> showNode(n, pc)
      }
      reformatted
    }

    val pc = new PrettyPrintContext()
    val mainProgram = show(p)
    // Don't forget the trivia after the last program node, i.e. trailing comments!
    val trailing = List(ctx.getTriviaByByteOffset(ctx.program.length, ctx.program.length))
    val finalProgram = (mainProgram ::: trailing).filter(!_.isNil)      
    super.pretty(defaultWidth, showList(finalProgram, pc))
  }

  def showOption[T <: Any](n: Option[T])(implicit ctx: ReformatterContext): List[RNode] = {
    n match {
      case Some(r) => showAny(r)
      case None => rn()
    }
  }

  def showAnnotations(annotations: Seq[PAnnotation])(implicit ctx: ReformatterContext): List[RNode] = {
    if (annotations.isEmpty) {
      List(RNil())
    } else {
      annotations.map(show(_)).reduce((acc, n) => acc ::: n)
    }
  }

  def showReturns(returns: Option[PMethodReturns])(implicit ctx: ReformatterContext): List[RNode] = {
    returns.map(a => rs() ::: show(a)).getOrElse(rn())
  }

  def showPresPosts(pres: PDelimited[_, _], posts: PDelimited[_, _])(implicit ctx: ReformatterContext): List[RNode] = {
    rne((if (pres.isEmpty) rn()
    else rlb() ::: show(pres)) :::
      (if (posts.isEmpty) rn()
      else rlb() ::: show(posts)
        )
    )
  }

  def showInvs(invs: PDelimited[_, _])(implicit ctx: ReformatterContext): List[RNode] = {
    rne(if (invs.isEmpty) rn() else rlb() ::: show(invs))
  }

  def showBody(body: Reformattable, newline: Boolean)(implicit ctx: ReformatterContext): List[RNode] = {
    if (newline) {
      rlb() ::: show(body)
    } else {
      rs() ::: show(body)
    }
  }

  def show(r: Reformattable)(implicit ctx: ReformatterContext): List[RNode] = {
    r match {
      case _: PLeaf => List(ctx.getTrivia(r.pos)) <> r.reformat(ctx)
      case _ => r.reformat(ctx)
    }
  }

  // We need this method because unfortunately PGrouped and PDelimited can have arbitrary generic parameters.
  def showAny(n: Any)(implicit ctx: ReformatterContext): List[RNode] = {
    n match {
      case p: Reformattable => show(p)
      case p: Option[Any] => showOption(p)
      case p: Seq[Any] => showSeq(p)
      case p: Right[Any, Any] => showAny(p.value)
      case p: Left[Any, Any] => showAny(p.value)
      case p: Iterable[Any] => if (p.isEmpty) List() else p.map(showAny).reduce((a, b) => a <> b)
    }
  }

  def showSeq(l: Seq[Any])(implicit ctx: ReformatterContext): List[RNode] = {
    if (l.isEmpty) {
      rn()
    } else {
      l.zipWithIndex.map(e => if (e._2 == 0) showAny(e._1) else rlb() <> showAny(e._1)).reduce(_ <> _)
    }
  }

  def reformatNodesNoSpace(n: PNode)(implicit ctx: ReformatterContext): List[RNode] = {
    n.subnodes.map(show(_)).reduce(_ <> _)
  }

  def reformatNodesWithSpace(n: PNode)(implicit ctx: ReformatterContext): List[RNode] = {
    n.subnodes.map(show(_)).reduce(_ <+> _)
  }
}