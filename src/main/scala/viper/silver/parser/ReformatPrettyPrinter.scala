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

class ReformatterContext(val program: String, val offsets: Seq[Int]) {
  var currentOffset: Int = 0

  def getByteOffset(p: HasLineColumn): Int = {
    val row = offsets(p.line - 1);
    row + p.column - 1
  }

  def getTrivia(pos: (ast.Position, ast.Position)): Seq[Trivia] = {
    pos._1 match {
      case p: HasLineColumn => {
        val p_offset = getByteOffset(p);
        getTriviaByByteOffset(p_offset)
      }
      case _ => Seq()
    }
  }

  def getTriviaByByteOffset(offset: Int): Seq[Trivia] = {
    if (currentOffset <= offset) {
      val str = program.substring(currentOffset, offset);
      this.currentOffset = offset;

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
    else linebreak <> show(pres)) <>
      (if (posts.isEmpty) nil
      else linebreak <> show(posts)
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
        val trivia = ctx.getTrivia(p.pos);

        var reformatted = nil
        var newlines = 0;
        var spaces = 0;

        for (t <- trivia) {
          t match {
            case p: PComment => {
              val lw = if (newlines > 1) linebreak else nil
              reformatted = reformatted <> lw <> p.reformat(ctx)
              newlines = 0
              spaces = 0
            }
            case _: PNewLine => newlines += 1
            case _: PSpace => spaces += 1
            case _ =>
          }
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

    trivia <@@@> r.reformat(ctx)
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
      l.map(showAny(_)).reduce(_ <> linebreak <> _)
    }
  }
}