package viper.silver.parser

import fastparse.Parsed
import viper.silver.ast
import viper.silver.ast.pretty.{Call, FastPrettyPrinterBase, PrettyPrintPrimitives}
import viper.silver.ast.HasLineColumn
import viper.silver.parser.FastParserCompanion.programTrivia
import viper.silver.parser.RLine.rl
import viper.silver.parser.RLineBreak.rlb
import viper.silver.parser.RNest.rne
import viper.silver.parser.RNil.rn
import viper.silver.parser.RSpace.rs

trait RNode {
  def isNil: Boolean
}

trait RWhitespace extends RNode

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

case class RHard(w: RWhitespace) extends RNode {
  override def isNil: Boolean = false
}

case class RSpace() extends RWhitespace {
  override def isNil: Boolean = false
}
object RSpace {
  def rs(): List[RNode] = List(RHard(RSpace()))
}

case class RLine() extends RWhitespace {
  override def isNil: Boolean = false
}
object RLine {
  def rl(): List[RNode] = List(RHard(RLine()))
}

case class RLineBreak() extends RWhitespace {
  override def isNil: Boolean = false
}
object RLineBreak {
  def rlb(): List[RNode] =List(RHard(RLineBreak()))
}

case class RDLineBreak() extends RWhitespace {
  override def isNil: Boolean = false
}
object RDLineBreak {
  def rdlb(): List[RNode] = List(RHard(RDLineBreak()))
}

sealed trait ReformatPrettyPrinterBase extends PrettyPrintPrimitives {
  val defaultIndent = 4
  val defaultWidth = 75

  implicit def char (c : Char) : Cont =
    if (c == '\n')
      line
    else
      text (c.toString)

  def space : Cont =
    char (' ')

  def dlinebreak : Cont =
    linebreak <> linebreak

  def line: Cont = line(" ")

  def linebreak : Cont =
    line ("\n")

  implicit class ContOps2(dl: List[RNode]) {
    def <>(dr: List[RNode]): List[RNode] =
      dl ::: dr

    def <+>(dr: List[RNode]): List[RNode] =
      if (dr.forall(_.isNil)) dl else if (dl.forall(_.isNil)) dr else dl ::: rs ::: dr

    def <@>(dr: List[RNode]): List[RNode] =
      if (dr.forall(_.isNil)) dl else if (dl.forall(_.isNil)) dr else dl ::: rl ::: dr

    def <->(dr: List[RNode]): List[RNode] =
      if (dr.forall(_.isNil)) dl else if (dl.forall(_.isNil)) dr else dl ::: rlb ::: dr
  }

  implicit class ContOps(dl: Cont) {
    def <>(dr: Cont) : Cont =
      (iw: IW) =>
        (c: TreeCont) => {
          Call(() =>
            for {
              t <- dr(iw)(c)
              t2 <- dl(iw)(t)
            } yield t2)
        }

    def <+> (dr : Cont) : Cont =
      dl <> space <> dr

    def <@> (dr: Cont) : Cont =
      if (dl == nil) dr else if (dr == nil) dl else dl <> line <> dr

    def <@@> (dr: Cont) : Cont =
      if (dl == nil) dr else if (dr == nil) dl else dl <> linebreak <> dr

    def <@@@> (dr: Cont) : Cont =
      if (dl == nil) dr else if (dr == nil) dl else dl <> dr

    def <@+> (dr: Cont) : Cont =
      if (dl == nil) dr else if (dr == nil) dl else dl <> dr

    def <+@> (dr: Cont) : Cont =
      if (dl == nil) dr else if (dr == nil) dl else dl <> space <> dr
  }
}

sealed trait Separator extends ReformatPrettyPrinterBase {
  def doc: Cont
}

case class SNil() extends Separator {
  override def doc: Cont = nil
}
case class SSpace() extends Separator {
  override def doc: Cont = space
}
case class SLine() extends Separator {
  override def doc: Cont = line
}
case class SLinebreak() extends Separator {
  override def doc: Cont = linebreak
}
case class SDLinebreak() extends Separator {
  override def doc: Cont = dlinebreak
}


trait Reformattable extends ReformatPrettyPrinterBase with Where {
  def reformat(implicit ctx: ReformatterContext): Cont
  def reformat2(implicit ctx: ReformatterContext2): List[RNode] = throw new IllegalAccessException(s"reformat2 not implemented ${getClass}")
}

trait ReformattableExpression extends ReformatPrettyPrinterBase {
  def reformatExp(implicit ctx: ReformatterContext): Cont
  def reformatExp2(implicit ctx: ReformatterContext2): List[RNode] = throw new IllegalAccessException(s"reformatExt2 not implemented ${getClass}")
}

class ReformatterContext(val program: String, val offsets: Seq[Int]) {
  var currentOffset: Int = 0

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

  def getTrivia(pos: (ast.Position, ast.Position), updateOffset: Boolean): Seq[Trivia] = {
    (pos._1, pos._2) match {
      case (p: HasLineColumn, q: HasLineColumn) => {
        val p_offset = getByteOffset(p);
        val q_offset = getByteOffset(q);
        getTriviaByByteOffset(p_offset, if (updateOffset) Some(q_offset) else None)
      }
      case _ => Seq()
    }
  }

  def getTriviaByByteOffset(offset: Int, updateOffset: Option[Int]): Seq[Trivia] = {
    if (currentOffset <= offset) {
      val str = program.substring(currentOffset, offset);
      currentOffset = currentOffset.max(offset);

      updateOffset match {
        case Some(o) => currentOffset = o
        case _ =>
      }

      fastparse.parse(str, programTrivia(_)) match {
        case Parsed.Success(value, _) => {
          value
        }
        case _: Parsed.Failure => Seq()
      }
    } else {
      Seq()
    };
  }
}

object ReformatPrettyPrinter extends ReformatPrettyPrinterBase {
  override val defaultIndent = 4

  def reformatProgram(p: PProgram): String = {
    println(s"${p}");
    implicit val ctx = new ReformatterContext(p.rawProgram, p.offsets)
    super.pretty(defaultWidth, show(p))
  }

  def showOption[T <: Any](n: Option[T], sep: Separator = SNil())(implicit ctx: ReformatterContext): Cont = {
    n match {
      case Some(r) => showAny(r, sep)
      case None => nil
    }
  }

  def showAnnotations(annotations: Seq[PAnnotation])(implicit ctx: ReformatterContext): Cont = {
    if (annotations.isEmpty) {
      nil
    } else {
      annotations.map(show(_)).foldLeft(nil)((acc, n) => acc <@@> n)
    }
  }

  def showReturns(returns: Option[PMethodReturns])(implicit ctx: ReformatterContext): Cont = {
    returns.map(a => nil <+> show(a)).getOrElse(nil)
  }

  def showPresPosts(pres: PDelimited[_, _], posts: PDelimited[_, _])(implicit ctx: ReformatterContext): Cont = {
    nest(defaultIndent, (if (pres.isEmpty) nil
    else show(pres, SLinebreak())) <>
      (if (posts.isEmpty) nil
      else show(posts, SLinebreak())
        )
    )
  }

  def showInvs(invs: PDelimited[_, _])(implicit ctx: ReformatterContext): Cont = {
    nest(defaultIndent, (if (invs.isEmpty) nil else show(invs, SLinebreak())))
  }

  def showBody(body: Reformattable, newline: Boolean)(implicit ctx: ReformatterContext): Cont = {
    if (newline) {
      show(body, SLinebreak())
    } else {
      show(body, SSpace())
    }
  }

  def show(r: Reformattable, sep: Separator = SNil())(implicit ctx: ReformatterContext): Cont = {
    val updatePos = r match {
      case _: PLeaf => true
      case _ => false
    }

//    println(s"separator: ${sep}");
//    println(s"pos: ${r.pos}");
//    println(s"node: ${r.getClass}");

    val trivia = ctx.getTrivia(r.pos, updatePos);

    var reformatted = nil
    var leadingNewlines = 0;
    var leadingSpaces = 0;
    var newlines = 0;
    var spaces = 0;
    var hasComment = false

    def getSep(newlines: Int, spaces: Int): Separator = {
      if (newlines > 1) SDLinebreak()
      else if (newlines > 0) SLinebreak()
      else if (spaces > 0) SSpace()
      else SNil()
    }

//    println(trivia);

    for (t <- trivia) {
      t match {
        case p: PComment => {
          val lw = if (!hasComment) {
            leadingNewlines = newlines;
            leadingSpaces = spaces;
            hasComment = true;
            nil
          } else  {
            getSep(newlines, spaces).doc
          }
          reformatted = reformatted <> lw <> p.display
          newlines = 0
          spaces = 0
        }
        case _: PNewLine => newlines += 1
        case _: PSpace => spaces += 1
        case _ =>
      }
    }

    val trailingNewlines = newlines;
    val trailingSpaces = spaces;

    val formattedTrivia = if (hasComment) {
      val leadingSep = getSep(leadingNewlines, leadingSpaces)
      val trailingSep = getSep(trailingNewlines, trailingSpaces)

      sep match {
        case _: SSpace => (if (leadingSep == SNil()) space else leadingSep.doc) <> reformatted <>
          (if (trailingSep == SNil()) space else trailingSep.doc)
        case _: SLinebreak => leadingSep.doc <> reformatted <> (if (trailingSep == SDLinebreak()) dlinebreak else linebreak)
        case _: SLine => leadingSep.doc <> reformatted <> (if (trailingSep == SDLinebreak()) dlinebreak else line)
        // `nil` and others
        case _ => leadingSep.doc <> reformatted <> trailingSep.doc
      }
    } else {
      println(s"${newlines}");
      if (newlines > 1 && sep == SLinebreak()) {
        dlinebreak
      } else {
        sep.doc
      }
    }

    formattedTrivia <@@@> r.reformat(ctx)
  }

  def showAny(n: Any, sep: Separator = SNil())(implicit ctx: ReformatterContext): Cont = {
    n match {
      case p: Reformattable => show(p, sep)
      case p: Option[Any] => showOption(p, sep)
      case p: Seq[Any] => showSeq(p, sep)
      case p: Right[Any, Any] => showAny(p.value, sep)
      case p: Left[Any, Any] => showAny(p.value, sep)
    }
  }

  def showSeq(l: Seq[Any], sep: Separator = SNil())(implicit ctx: ReformatterContext): Cont = {
    if (l.isEmpty) {
      nil
    } else {
      l.zipWithIndex.map(e => if (e._2 == 0) showAny(e._1, sep) else showAny(e._1, SLinebreak())).reduce(_ <> _)
    }
  }
}

class ReformatterContext2(val program: String, val offsets: Seq[Int]) {
  var currentOffset: Int = 0

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

  def getTrivia(pos: (ast.Position, ast.Position), updateOffset: Boolean): List[RNode] = {
    (pos._1, pos._2) match {
      case (p: HasLineColumn, q: HasLineColumn) => {
        val p_offset = getByteOffset(p);
        val q_offset = getByteOffset(q);
        getTriviaByByteOffset(p_offset, if (updateOffset) Some(q_offset) else None)
      }
      case _ => List()
    }
  }

  def getTriviaByByteOffset(offset: Int, updateOffset: Option[Int]): List[RNode] = {
    if (currentOffset <= offset) {
      val str = program.substring(currentOffset, offset);
      currentOffset = currentOffset.max(offset);

      updateOffset match {
        case Some(o) => currentOffset = o
        case _ =>
      }

      fastparse.parse(str, programTrivia(_)) match {
        case Parsed.Success(value, _) => {
          value.map(_.content).toList
        }
        case _: Parsed.Failure => List()
      }
    } else {
      List()
    };
  }
}

object ReformatPrettyPrinter2 extends ReformatPrettyPrinterBase {
  def reformatProgram2(p: PProgram): String = {
    implicit val ctx = new ReformatterContext2(p.rawProgram, p.offsets)

    def showList(p: List[RNode]): Cont = if (p.isEmpty) nil else p.map(n => n match {
      case RNil() => nil
      case RText(t: String) => {
        println(s"Found text: ${}, ${}", t, t.length)
        text(t)
      }
      case RSpace() => space
      case RHard(w) => showList(List(w))
      case RGroup(l: List[RNode]) => group(showList(l))
      case RNest(l: List[RNode]) => nest(defaultIndent, showList(l))
      case RLine() => line
      case RLineBreak() => linebreak
      case RDLineBreak() => linebreak <> linebreak
    }).reduce(_ <> _)

    val list = show2(p).filter(!_.isNil)
    println(s"List: ${list}")
    super.pretty(defaultWidth, showList(list))
  }

  def showOption2[T <: Any](n: Option[T])(implicit ctx: ReformatterContext2): List[RNode] = {
    n match {
      case Some(r) => showAny2(r)
      case None => rn
    }
  }

  def showAnnotations2(annotations: Seq[PAnnotation])(implicit ctx: ReformatterContext2): List[RNode] = {
    if (annotations.isEmpty) {
      List(RNil())
    } else {
      annotations.map(show2(_)).reduce((acc, n) => acc ::: n)
    }
  }

  def showReturns2(returns: Option[PMethodReturns])(implicit ctx: ReformatterContext2): List[RNode] = {
    returns.map(a => rs ::: show2(a)).getOrElse(rn)
  }

  def showPresPosts2(pres: PDelimited[_, _], posts: PDelimited[_, _])(implicit ctx: ReformatterContext2): List[RNode] = {
    rne((if (pres.isEmpty) rn
    else rlb ::: show2(pres)) :::
      (if (posts.isEmpty) rn
      else rlb ::: show2(posts)
        )
    )
  }

  def showInvs2(invs: PDelimited[_, _])(implicit ctx: ReformatterContext2): List[RNode] = {
    rne(if (invs.isEmpty) rn else rlb ::: show2(invs))
  }

  def showBody2(body: Reformattable, newline: Boolean)(implicit ctx: ReformatterContext2): List[RNode] = {
    if (newline) {
      rlb ::: show2(body)
    } else {
      rs ::: show2(body)
    }
  }

  def show2(r: Reformattable)(implicit ctx: ReformatterContext2): List[RNode] = {
    val updatePos = r match {
      case _: PLeaf => true
      case _ => false
    }

    val trivia = ctx.getTrivia(r.pos, updatePos);

    trivia ::: r.reformat2(ctx)
  }

  def showAny2(n: Any)(implicit ctx: ReformatterContext2): List[RNode] = {
    n match {
      case p: Reformattable => show2(p)
      case p: Option[Any] => showOption2(p)
      case p: Seq[Any] => showSeq2(p)
      case p: Right[Any, Any] => showAny2(p.value)
      case p: Left[Any, Any] => showAny2(p.value)
    }
  }

  def showSeq2(l: Seq[Any])(implicit ctx: ReformatterContext2): List[RNode] = {
    if (l.isEmpty) {
      rn
    } else {
      l.zipWithIndex.map(e => if (e._2 == 0) showAny2(e._1) else rlb ::: showAny2(e._1)).reduce(_ ::: _)
    }
  }
}