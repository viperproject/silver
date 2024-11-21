package viper.silver.parser

import fastparse.Parsed
import viper.silver.ast
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.ast.{HasLineColumn}
import viper.silver.parser.FastParserCompanion.programTrivia

sealed trait Separator extends FastPrettyPrinterBase {
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


trait Reformattable extends FastPrettyPrinterBase with Where {
  def reformat(implicit ctx: ReformatterContext): Cont
}

trait ReformattableExpression extends FastPrettyPrinterBase {
  def reformatExp(implicit ctx: ReformatterContext): Cont
}

class ReformatterContext(val program: String, val offsets: Seq[Int]) {
  var currentOffset: Int = 0
  var currentSeparator: Separator = SNil()

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

//  def registerSeparator(sep: Separator) = {
//    currentSeparator match {
//      case SNil() => currentSeparator = sep
//      case SSpace() => sep match {
//        case SNil() => {}
//        case _ => currentSeparator = sep
//      }
//      case SLine() | SLinebreak() => sep match {
//        case SLine() | SLinebreak() | SDLinebreak() => currentSeparator = sep
//        case _ => {}
//      }
//      case _ => {}
//    }
//  }

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

object ReformatPrettyPrinter extends FastPrettyPrinterBase {
  override val defaultIndent = 4

  def reformatProgram(p: PProgram): String = {
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

    println(s"separator: ${sep}");
    println(s"pos: ${r.pos}");
    println(s"node: ${r.getClass}");

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

    println(trivia);

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