// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.
//
// Copyright (c) 2011-2019 ETH Zurich.

package viper.silver.parser

import java.nio.file.Path

import scala.annotation.tailrec
import scala.language.implicitConversions
import fastparse.{WhitespaceApi, all}
import fastparse.core.Implicits
import fastparse.core.Implicits.{Repeater, Sequencer}
import fastparse.all._
import fastparse.core.{Mutable, ParseCtx, Parser}
import fastparse.parsers.Combinators.{Repeat, Rule}
import fastparse.parsers.Terminals.Pass
import fastparse.utils.ReprOps
import viper.silver.ast.HasLineColumn

case class FilePosition(file: Path, vline: Int, col: Int) extends util.parsing.input.Position with HasLineColumn
{
  override lazy val line = vline
  override lazy val column = col
  override lazy val lineContents = toString
  override lazy val toString = s"${file.getFileName}@$vline.$col"
}

trait PosComputer {
  def computeFrom(index: Int) : (Int, Int) = {
    var left = index
    var i = 0
    val arr = FastParser._lines
    while (i < arr.length && left >= arr(i)){
      left -= arr(i)
      i += 1
    }
    val r1 = (i + 1, left + 1)
    r1
  }
}
/**
  * This class is a custom class for parser and has added FastPosition
  * support.
  * */
class PosRepeat[T, +R, Elem, Repr](p: Parser[T, Elem, Repr], min: Int, max: Int, delimiter: Parser[_, Elem, Repr])
                                  (implicit ev: Implicits.Repeater[T, R], repr: ReprOps[Elem, Repr])
                                  extends Repeat[T, R, Elem, Repr](p, min, max, delimiter) with PosComputer{

  override def parseRec(cfg: ParseCtx[Elem, Repr], index: Int) = {
    @tailrec def rec(index: Int,
                     del: Parser[_, Elem, Repr],
                     lastFailure: Mutable.Failure[Elem, Repr],
                     acc: ev.Acc,
                     cut: Boolean,
                     count: Int): Mutable[R, Elem, Repr] = {
      del.parseRec(cfg, index) match{
        case f1: Mutable.Failure[Elem, Repr] =>
          val cut1 = f1.cut
          if (cut1) failMore(f1, index, cfg.logDepth, cut = true)
          else passInRange(cut, f1, index, ev.result(acc), count)

        case Mutable.Success(_, index0, _, cut0)  =>
          p.parseRec(cfg, index0) match{
            case f2: Mutable.Failure[Elem, Repr] =>
              val cut2 = f2.cut
              if (cut2 | cut0) failMore(f2, index0, cfg.logDepth, cut = true)
              else passInRange(cut | cut0, f2, index, ev.result(acc), count)

            case Mutable.Success(value1, index1, _, cut1)  =>
              ev.accumulate(value1, acc)
              val counted = count + 1
              val start1 = computeFrom(index0)
              val end1 = computeFrom(index1)
              viper.silver.FastPositions.setStart(value1, FilePosition(FastParser._file, start1._1, start1._2))
              viper.silver.FastPositions.setFinish (value1, FilePosition(FastParser._file, end1._1, end1._2))
              if (counted < max)
                rec(index1, delimiter, lastFailure, acc, cut0 | cut1, counted)
              else
                passInRange(cut0 | cut1, lastFailure, index1, ev.result(acc), counted)
          }
      }
    }

    def passInRange(cut: Boolean,
                    lastFailure: Mutable.Failure[Elem, Repr],
                    finalIndex: Int,
                    acc: R,
                    count: Int) = {
      if (min <= count) {
        val parsers =
          if (null == lastFailure) Set.empty[Parser[_, Elem, Repr]]
          else lastFailure.traceParsers
        success(cfg.success, acc, finalIndex, parsers, cut)
      } else failMore(lastFailure, index, cfg.logDepth, cut = cut)
    }

    // don't call the parseRec at all, if max is "0", as our parser corresponds to `Pass` in that case.
    if (max == 0 ) {
      success(cfg.success, ev.result(ev.initial), index, Set.empty[Parser[_, Elem, Repr]], false)
    } else {
      rec(index, Pass[Elem, Repr], null, ev.initial, false, 0)
    }
  }
  override def toString = {
    val things = Seq(
      if (min == 0) None else Some(min),
      if (delimiter == Pass[Elem, Repr]) None else Some("sep = " + delimiter),
      if (max == Int.MaxValue) None else Some("max = " + max)
    ).flatten.mkString(", ")
    if (things.isEmpty) opWrap(p) + ".rep"
    else s"${opWrap(p)}.rep($things)"
  }
}

class PosCustomSequence[+T, +R, +V](WL: P0, p0: P[T], p: P[V], cut: Boolean)
                                   (implicit ev: Sequencer[T, V, R]) extends WhitespaceApi.CustomSequence(WL, p0, p, cut)(ev) with PosComputer{


  override def parseRec(cfg: all.ParseCtx, index: Int) = {
    p0.parseRec(cfg, index) match {
      case f: all.Mutable.Failure => failMore(f, index, cfg.logDepth, f.traceParsers, false)
      case Mutable.Success(value0, index0, traceParsers0, cut0) =>
        val start0 = computeFrom(index)
        val end0 = computeFrom(index0)
        viper.silver.FastPositions.setStart (value0, FilePosition(FastParser._file, start0._1, start0._2))
        viper.silver.FastPositions.setFinish (value0, FilePosition(FastParser._file, end0._1, end0._2))
        WL.parseRec(cfg, index0) match {
          case f1: all.Mutable.Failure => failMore(f1, index, cfg.logDepth)
          case Mutable.Success(value1, index1, traceParsers1, cut1) =>
            p.parseRec(cfg, index1) match {
              case f: all.Mutable.Failure => failMore(
                f, index1, cfg.logDepth,
                mergeTrace(cfg.traceIndex, traceParsers0, f.traceParsers),
                cut | cut0
              )
              case Mutable.Success(value2, index2, traceParsers2, cut2) =>
                val start1 = computeFrom(index1)
                val end1 = computeFrom(index2)
                viper.silver.FastPositions.setStart (value2, FilePosition(FastParser._file, start1._1, start1._2))
                viper.silver.FastPositions.setFinish (value2, FilePosition(FastParser._file, end1._1, end1._2))
                val (newIndex, newCut) =
                  if (index2 > index1 || index1 == cfg.input.length) (index2, cut | cut0 | cut1 | cut2)
                  else (index0, cut | cut0 | cut2)

                success(
                  cfg.success,
                  ev.apply(value0, value2),
                  newIndex,
                  mergeTrace(cfg.traceIndex, traceParsers0, traceParsers2),
                  newCut
                )
            }
        }
    }
  }

}

class PositionRule[+T, Elem, Repr](override val name: String, override val p: () => Parser[T, Elem, Repr])
                                  (implicit repr: ReprOps[Elem, Repr])
                                  extends Rule[T, Elem, Repr](name, p) with PosComputer{
  lazy val pCached = p()

  override def parseRec(cfg: ParseCtx[Elem, Repr], index: Int) = {
    if (cfg.instrument == null) {
      pCached.parseRec(cfg, index) match{
        case f: Mutable.Failure[Elem, Repr] => failMore(f, index, cfg.logDepth)
        case s: Mutable.Success[T, Elem, Repr] =>
          val start = computeFrom(index)
          val end = computeFrom(s.index)
          viper.silver.FastPositions.setStart (s.value, FilePosition(FastParser._file, start._1, start._2))
          viper.silver.FastPositions.setFinish (s.value, FilePosition(FastParser._file, end._1, end._2))
          s
      }
    } else {
      lazy val res = pCached.parseRec(cfg, index) match{
        case f: Mutable.Failure[Elem, Repr] => failMore(f, index, cfg.logDepth)
        case s: Mutable.Success[T, Elem, Repr] =>
          val start = computeFrom(index)
          val end = computeFrom(s.index)
          viper.silver.FastPositions.setStart (s.value, FilePosition(FastParser._file, start._1, start._2))
          viper.silver.FastPositions.setFinish (s.value, FilePosition(FastParser._file, end._1, end._2))

          s
      }
      cfg.instrument(this, index, () => res.toResult)
      res
    }
  }
}

trait PosParser[Elem, Repr] {
  /**
    * This trait contains all the new Definitions of the parser 'P' , '~' , 'rep'
    * which override the normal definitions with 'PositionRule' to add support for
    * FastPosition in the parser.
    * */
  var _file: Path = null

  def P[T](p: => Parser[T, Elem, Repr])(implicit name: sourcecode.Name, repr: ReprOps[Elem, Repr]): Parser[T, Elem, Repr] =
    new PositionRule(name.value, () => p)

  def PWrapper(WL: P0) = new PWrapper(WL)

  class PWhitespaceApi[V](p0: P[V], WL: P0) extends WhitespaceApi[V](p0, WL){

    override def repX[R](implicit ev: Repeater[V, R]): all.Parser[R] = new PosRepeat(p0, 0, Int.MaxValue, all.Pass)

    override def rep[R](implicit ev: Repeater[V, R]): all.Parser[R] = new PosRepeat(p0, 0, Int.MaxValue, NoCut(WL))

    override def repX[R](min: Int = 0, sep: all.Parser[_] = all.Pass, max: Int = Int.MaxValue)
                        (implicit ev: Repeater[V, R]): all.Parser[R] =  new PosRepeat(p0, min, max, sep)

    override def rep[R](min: Int = 0, sep: all.Parser[_] = all.Pass, max: Int = Int.MaxValue, exactly: Int = -1)
                       (implicit ev: Repeater[V, R]): all.Parser[R] = {
      new PosRepeat(p0, if (exactly < 0) min else exactly, if (exactly < 0) max else exactly,
                    if (sep != all.Pass) NoCut(WL) ~ sep ~ NoCut(WL) else NoCut(WL))
    }

    override def ~[V2, R](p: all.Parser[V2])(implicit ev: Sequencer[V, V2, R]): all.Parser[R] = {
      assert(p != null)
      new PosCustomSequence[V, R, V2](WL, if (p0 != WL) p0 else all.Pass.asInstanceOf[P[V]], p, cut=false)(ev)
    }

    override def ~/[V2, R](p: P[V2])
                          (implicit ev: Sequencer[V, V2, R])
    : P[R] = {
      assert(p != null)
      new PosCustomSequence(WL, if (p0 != WL) p0 else all.Pass.asInstanceOf[P[V]], p, cut=true)(ev)
    }
  }
  class PWrapper(WL: P0){
    implicit def parserApi[T, V](p0: T)(implicit c: T => P[V]): PWhitespaceApi[V] =
      new PWhitespaceApi[V](p0, WL)
  }
}

