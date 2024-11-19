package viper.silver.parser

import fastparse.Parsed
import viper.silver.ast
import viper.silver.ast.pretty.FastPrettyPrinterBase
import viper.silver.ast.{HasLineColumn, LineColumnPosition, Position}
import viper.silver.parser.FastParserCompanion.programTrivia
import viper.silver.plugin.standard.adt.PAdtConstructor

import scala.::
import scala.util.control.Breaks.{break, breakable}

trait Reformattable extends FastPrettyPrinterBase {
  def reformat(ctx: ReformatterContext): Cont
}

trait ReformattableExpression extends FastPrettyPrinterBase {
  def reformatExp(ctx: ReformatterContext): Cont
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
    var positions: Map[ast.Position, ast.Position] = Map(LineColumnPosition(1, 1) -> leavePositions.headOption.map(p => p._1).getOrElse(LineColumnPosition(1, 1)))

    if (leavePositions.length > 1) {
      leavePositions.sliding(2).foreach {
        case Seq(a, b) =>  positions += (a._2 -> b._1)
      }
    }

    val ctx = new ReformatterContext(p.rawProgram, p.offsets, positions)
    super.pretty(defaultWidth, show(p, ctx))
  }

  def showOption[T <: Any](n: Option[T], ctx: ReformatterContext): Cont = {
    n match {
      case Some(r) => showAny(r, ctx)
      case None => nil
    }
  }

  def showAnnotations(annotations: Seq[PAnnotation], ctx: ReformatterContext): Cont = {
    if (annotations.isEmpty) {
      nil
    } else {
      annotations.map(show(_, ctx)).foldLeft(nil)((acc, n) => acc <@@> n)
    }
  }

  def showReturns(returns: Option[PMethodReturns], ctx: ReformatterContext): Cont = {
    returns.map(a => nil <+> show(a, ctx)).getOrElse(nil)
  }

  def showPresPosts(pres: PDelimited[_, _], posts: PDelimited[_, _], ctx: ReformatterContext): Cont = {
    nest(defaultIndent, (if (pres.isEmpty) nil
    else line <> show(pres, ctx)) <>
      (if (posts.isEmpty) nil
      else line <> show(posts, ctx)
        )
    )
  }

  def showInvs(invs: PDelimited[_, _], ctx: ReformatterContext): Cont = {
    nest(defaultIndent, (if (invs.isEmpty) nil else line <> show(invs, ctx)))
  }

  def showBody(body: Cont, newline: Boolean): Cont = {
    if (newline) {
      linebreak <> body
    } else {
      nil <+> body
    }
  }

  def formatTrivia(trivia: Seq[Trivia], ctx: ReformatterContext): Cont = {
    trivia.filter({
        case _: PComment => true
        case _ => false
      })
      .foldLeft(nil)(_ <@@@> show(_, ctx))
  }

  def show(r: Reformattable, ctx: ReformatterContext): Cont = {
    println(s"${r.getClass}");
    println(s"${r}");
    val trivia = r match {
      case p: PLeaf => {
        val trivia = ctx.posMap.get(p.pos._2).map(end => {
          println(s"${p}");
          println(s"${p.pos._2}, ${end}");
          ctx.getTrivia(p.pos._2, end)
        }).getOrElse({

          Seq()
        });
        println(trivia)
        val findNewlines = (trivia: Seq[Trivia]) => {
          var count = 0;
          breakable {
            for (el <- trivia) {
              el match {
                case _: PComment => break
                case _: PNewLine => count += 1
                case _ =>
              }
            }
          }

          if (count > 1) linebreak else nil
        }

        val lw = findNewlines(trivia);
        val tw = findNewlines(trivia.reverse);
        val hasComment = trivia exists {
          case _: PComment => true
          case _ => false
        }

        if (hasComment) {
          lw <> formatTrivia(trivia, ctx) <> tw
        } else  {
          lw
        }

      };
      case _ => nil
    }

    r.reformat(ctx) <> trivia
  }

  def showAny(n: Any, ctx: ReformatterContext): Cont = {
    n match {
      case p: Reformattable => show(p, ctx)
      case p: Option[Any] => showOption(p, ctx)
      case p: Seq[Any] => showSeq(p, ctx)
      case p: Right[Any, Any] => showAny(p.value, ctx)
      case p: Left[Any, Any] => showAny(p.value, ctx)
    }
  }

  def showSeq(l: Seq[Any], ctx: ReformatterContext): Cont = {
    if (l.isEmpty) {
      nil
    } else {
      val sep = l.head match {
        case _: PAdtConstructor => linebreak
        case _ => linebreak
      }
      l.map(showAny(_, ctx)).reduce(_ <> sep <> _)
    }
  }
}