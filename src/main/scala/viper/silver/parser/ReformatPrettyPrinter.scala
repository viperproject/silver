package viper.silver.parser

import fastparse.Parsed
import viper.silver.ast
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.ast.{HasLineColumn, LineColumnPosition, Position}
import viper.silver.parser.FastParserCompanion.programTrivia
import viper.silver.plugin.standard.adt.PAdtConstructor

trait Reformattable extends FastPrettyPrinterBase {
  def reformat(implicit ctx: ReformatterContext): Cont
}

trait ReformattableExpression extends FastPrettyPrinterBase {
  def reformatExp(implicit ctx: ReformatterContext): Cont
}

class ReformatterContext(val program: String, val offsets: Seq[Int], val posMap: Map[Position, Position]) {
  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

  def getTrivia(start: ast.Position, end: ast.Position): Seq[Trivia] = {
    (start, end) match {
      case (p: HasLineColumn, q: HasLineColumn) => {
        val p_offset = getByteOffset(p);
        val q_offset = getByteOffset(q);
        getTriviaByByteOffset(p_offset, q_offset)
      }
      case _ => Seq()
    }
  }

  def getTriviaByByteOffset(startOffset: Int, endOffset: Int): Seq[Trivia] = {
    if (startOffset < endOffset) {
      val str = program.substring(startOffset, endOffset);

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
    def collectLeavePositions(p: PNode): Seq[(ast.Position, ast.Position)] = {
      p match {
        case p: PLeaf => Seq(p.pos)
        case _ => p.subnodes.flatMap(collectLeavePositions)
      }
    }
    val leavePositions = collectLeavePositions(p)
    var positions: Map[ast.Position, ast.Position] = Map(leavePositions.headOption.map(p => p._1).getOrElse(LineColumnPosition(1, 1)) -> LineColumnPosition(1, 1))

    if (leavePositions.length > 1) {
      leavePositions.sliding(2).foreach {
        case Seq(a, b) =>  positions += (b._1 -> a._2)
      }
    }

    implicit val ctx = new ReformatterContext(p.rawProgram, p.offsets, positions)
    super.pretty(defaultWidth, show(p))
  }

  def showOption[T <: Any](n: Option[T])(implicit ctx: ReformatterContext): Cont = {
    n match {
      case Some(r) => showAny(r)
      case None => nil
    }
  }

  def showAnnotations(annotations: Seq[PAnnotation])(implicit ctx: ReformatterContext): Cont = {
    if (annotations.isEmpty) {
      nil
    } else {
      annotations.map(show).foldLeft(nil)((acc, n) => acc <@@> n)
    }
  }

  def showReturns(returns: Option[PMethodReturns])(implicit ctx: ReformatterContext): Cont = {
    returns.map(a => nil <+> show(a)).getOrElse(nil)
  }

  def showPresPosts(pres: PDelimited[_, _], posts: PDelimited[_, _])(implicit ctx: ReformatterContext): Cont = {
    nest(defaultIndent, (if (pres.isEmpty) nil
    else line <> show(pres)) <>
      (if (posts.isEmpty) nil
      else line <> show(posts)
        )
    )
  }

  def showInvs(invs: PDelimited[_, _])(implicit ctx: ReformatterContext): Cont = {
    nest(defaultIndent, (if (invs.isEmpty) nil else line <> show(invs)))
  }

  def showBody(body: Cont, newline: Boolean): Cont = {
    if (newline) {
      linebreak <> body
    } else {
      nil <+> body
    }
  }

  def show(r: Reformattable)(implicit ctx: ReformatterContext): Cont = {
    val trivia = r match {
      case p: PLeaf => {
        val trivia = ctx.posMap.get(p.pos._1).map(end => {
          ctx.getTrivia(end, p.pos._2)
        }).getOrElse({
          Seq()
        });

        println(s"Trivia: ${trivia}");

        var reformatted = nil
        var newlines = 0;
        var spaces = 0;

        for (t <- trivia) {
          t match {
            case p: PComment => {
              val lw = if (newlines > 0) linebreak else if(spaces > 0) space else nil
              reformatted = reformatted <> lw <> group(p.reformat(ctx))
              newlines = 0
              spaces = 0
            }
            case _: PNewLine => newlines += 1
            case _: PSpace => spaces += 1
            case _ =>
          }
        }

        if (newlines > 0) {
          reformatted = reformatted <> linebreak
        }

        val hasComment = trivia exists {
          case _: PComment => true
          case _ => false
        }

        if (hasComment) {
          reformatted
        } else {
          if (newlines > 1) {
            linebreak
          } else {
            nil
          }
        }
      };
      case _ => nil
    }

    trivia <> r.reformat(ctx)
  }

  def showAny(n: Any)(implicit ctx: ReformatterContext): Cont = {
    n match {
      case p: Reformattable => show(p)
      case p: Option[Any] => showOption(p)
      case p: Seq[Any] => showSeq(p)
      case p: Right[Any, Any] => showAny(p.value)
      case p: Left[Any, Any] => showAny(p.value)
    }
  }

  def showSeq(l: Seq[Any])(implicit ctx: ReformatterContext): Cont = {
    if (l.isEmpty) {
      nil
    } else {
      val sep = l.head match {
        case _: PAdtConstructor => linebreak
        case _ => linebreak
      }
      l.map(showAny(_)).reduce(_ <> sep <> _)
    }
  }
}