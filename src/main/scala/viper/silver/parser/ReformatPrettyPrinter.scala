package viper.silver.parser

import fastparse.Parsed
import viper.silver.ast
import viper.silver.ast.HasLineColumn
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.parser.FastParserCompanion.programTrivia
import viper.silver.parser.RLine.rl
import viper.silver.parser.RLineBreak.rlb
import viper.silver.parser.RNest.rne
import viper.silver.parser.RNil.rn
import viper.silver.parser.RSpace.rs

import scala.collection.mutable.ArrayBuffer

trait RNode {
  def isNil: Boolean
}
trait RCommentFragment
trait RWhitespace extends RNode with RCommentFragment

case class RNil() extends RNode {
  override def isNil: Boolean = true
}

object RNil {
  def rn(): List[RNode] = List(RNil())
}

case class RText(text: String) extends RNode {
  override def isNil: Boolean = text.isEmpty
}

object RText {
  def rt(text: String): List[RNode] = List(RText(text))
}

case class RTrivia(l: List[RCommentFragment]) extends RNode {
  override def isNil: Boolean = l.isEmpty

  def hasComment(): Boolean = l.exists(_ match {
    case RComment(_) => true
    case _ => false
  })

  def lw(): Option[RWhitespace] = l.headOption.flatMap(_ match {
    case w: RWhitespace => Some(w)
    case _ => None
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

object RNest {
  def rne(l: List[RNode]): List[RNode] = List(RNest(l))
}

case class RGroup(l: List[RNode]) extends RNode {
  override def isNil: Boolean = l.forall(_.isNil)
}

object RGroup {
  def rg(l: List[RNode]): List[RNode] = List(RGroup(l))
}

case class RSpace() extends RWhitespace with RCommentFragment {
  override def isNil: Boolean = false
}

object RSpace {
  def rs(): List[RNode] = List(RSpace())
}

case class RLine() extends RWhitespace {
  override def isNil: Boolean = false
}

object RLine {
  def rl(): List[RNode] = List(RLine())
}

case class RLineBreak() extends RWhitespace with RCommentFragment {
  override def isNil: Boolean = false
}

object RLineBreak {
  def rlb(): List[RNode] = List(RLineBreak())
}

case class RDLineBreak() extends RWhitespace with RCommentFragment {
  override def isNil: Boolean = false
}

object RDLineBreak extends RWhitespace {
  def rdlb(): List[RNode] = List(RDLineBreak())

  override def isNil: Boolean = false
}

sealed trait ReformatPrettyPrinterBase extends FastPrettyPrinterBase {
  override val defaultIndent = 4
  override val defaultWidth = 75
}

trait ReformattableBase {
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

trait Reformattable extends ReformattableBase with Where {
  def reformat(implicit ctx: ReformatterContext): List[RNode]
}

trait ReformattableExpression extends ReformattableBase {
  def reformatExp(implicit ctx: ReformatterContext): List[RNode]
}

class ReformatterContext(val program: String, val offsets: Seq[Int]) {
  var currentOffset: Int = 0

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

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

  def getTriviaByByteOffset(offset: Int, updateOffset: Int): RTrivia = {
    if (currentOffset <= offset) {
      val str = program.substring(currentOffset, offset);
      currentOffset = updateOffset

      fastparse.parse(str, programTrivia(_)) match {
        case Parsed.Success(value, _) => {
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
              }
              case _: PNewLine => newlines += 1
              case _: PSpace => spaces += 1
              case _ => {}
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

class PrintContext {
  var whitespace: Option[RWhitespace] = None

  def register(w: RWhitespace): Unit = {
    whitespace match {
      case None => whitespace = Some(w)
      case Some(_: RLineBreak) => w match {
        case _: RLineBreak => whitespace = Some(RDLineBreak)
        case _: RDLineBreak => whitespace = Some(RDLineBreak)
      }
      case Some(_) => whitespace = Some(w)
    }
  }
}

object ReformatPrettyPrinter extends ReformatPrettyPrinterBase {
  def reformatProgram(p: PProgram): String = {
    implicit val ctx = new ReformatterContext(p.rawProgram, p.offsets)

    def showWhitespace(w: Option[RWhitespace]): Cont = {
      w match {
        case None => nil
        case Some(RSpace()) => space
        case Some(RLine()) => line
        case Some(RLineBreak()) => linebreak
        case Some(RDLineBreak()) => linebreak <> linebreak
      }
    }

    def showTrivia(p: RTrivia): Cont = {
      if (p.l.isEmpty) {
        nil
      } else {
        p.l.map(t => t match {
          case w: RWhitespace => showWhitespace(Some(w))
          case p: RComment => text(p.comment.str)
        }).reduce((acc, n) => acc <> n)
      }
    }

    def showNode(p: RNode, pc: PrintContext): Cont = {
      p match {
        case RNil() => nil
        case w: RWhitespace => {
          pc.register(w)
          showWhitespace(Some(w))
        }
        case RText(t: String) => {
          pc.whitespace = None
          text(t)
        }
        case t: RTrivia => {
          if (t.hasComment()) {
//            println(t);
            pc.whitespace match {
              case None => showTrivia(t)
              case Some(w: RLineBreak) => if (t.l.headOption == Some(RDLineBreak())) {
                  showTrivia(t.replacedLw(RLineBreak()))
                } else {
                 showTrivia(t.trimmedLw())
              }
              case Some(w: RSpace) => if (t.l.headOption == Some(RSpace())) {
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
        case RNest(l: List[RNode]) => {
//          println(s"nested ${p}")
          nest(defaultIndent, showList(l, pc))
        }
      }
    }

    def showList(p: List[RNode], pc: PrintContext): Cont = {
      var reformatted = nil
      for (n <- p) {
        reformatted = reformatted <> showNode(n, pc)
      }
      reformatted
    }

    val pc = new PrintContext()
    val mainProgram = show(p)
    val trailing = List(ctx.getTriviaByByteOffset(ctx.program.length, ctx.program.length))
    val finalProgram = (mainProgram ::: trailing).filter(!_.isNil)
//    println(s"IR: ${finalProgram}")
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
//    println(s"pos: ${r.pos}, node: ${r.getClass}")
    r match {
      case _: PLeaf => List(ctx.getTrivia(r.pos)) ::: r.reformat(ctx)
      case _ => r.reformat(ctx)
    }
  }

  def showAny(n: Any)(implicit ctx: ReformatterContext): List[RNode] = {
    n match {
      case p: Reformattable => show(p)
      case p: Option[Any] => showOption(p)
      case p: Seq[Any] => showSeq(p)
      case p: Right[Any, Any] => showAny(p.value)
      case p: Left[Any, Any] => showAny(p.value)
    }
  }

  def showSeq(l: Seq[Any])(implicit ctx: ReformatterContext): List[RNode] = {
    if (l.isEmpty) {
      rn()
    } else {
      l.zipWithIndex.map(e => if (e._2 == 0) showAny(e._1) else rlb() ::: showAny(e._1)).reduce(_ ::: _)
    }
  }
}