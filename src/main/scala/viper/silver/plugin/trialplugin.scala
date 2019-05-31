package viper.silver.plugin

import java.nio.file.Path

import fastparse.all._
import fastparse.core.Implicits.{Repeater, Sequencer}
import fastparse.core.Parser
import fastparse.utils.ReprOps
import fastparse.{WhitespaceApi, all, noApi}
import viper.silver.parser.FastParser._
import viper.silver.parser.{PExp, PFunction, _}
//import White.parserApi
//import White._

trait PosPParser[Elem, Repr] {
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



object trialplugin  extends PosPParser[Char, String] {


    lazy val functionDecl: noApi.P[PFunction] = FastParser.P("function" ~/ idndef ~ "(" ~ formalArgList ~ ")" ~ ":" ~ typ ~ pre.rep ~
      post.rep ~ ("{" ~ exp ~ "}").?).map { case (a, b, c, d, e, f) => PFunction(a, b, c, d, e, f) }


    lazy val atom: noApi.P[PExp] = FastParser.P(integer | booltrue | boolfalse | nul | old
      | result | unExp
      | "(" ~ exp ~ ")" | accessPred | inhaleExhale | perm | let | quant | forperm | unfolding | applying
      | setTypedEmpty | explicitSetNonEmpty | multiSetTypedEmpty | explicitMultisetNonEmpty | seqTypedEmpty
      | seqLength | explicitSeqNonEmpty | seqRange | fapp | typedFapp | idnuse)
}
